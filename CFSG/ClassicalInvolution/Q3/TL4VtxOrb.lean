module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26X
public import CFSG.ClassicalInvolution.Q3.TL4SepDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

variable {Q : Type} [Group Q] {Φ : Set (Subgroup Q)}

@[expose] noncomputable def orbGrp (Φ : Set (Subgroup Q)) (K : Subgroup Q) : Subgroup Q :=
  ⨆ g : ↥(omegaGen Φ), conjSub (g : Q) K

theorem conjSub_le_orbGrp (K : Subgroup Q) (g : ↥(omegaGen Φ)) :
    conjSub (g : Q) K ≤ orbGrp Φ K :=
  le_iSup (fun g : ↥(omegaGen Φ) => conjSub (g : Q) K) g

theorem le_orbGrp (K : Subgroup Q) : K ≤ orbGrp Φ K := by
  have h := conjSub_le_orbGrp (Φ := Φ) K 1
  rwa [OneMemClass.coe_one, conjSub_one] at h

theorem orbGrp_le (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ) :
    orbGrp Φ K ≤ omegaGen Φ :=
  iSup_le fun _ => le_omegaGen (hcl _ K hK)

theorem conjSub_orbGrp_le {K : Subgroup Q} {g : Q} (hg : g ∈ omegaGen Φ) :
    conjSub g (orbGrp Φ K) ≤ orbGrp Φ K := by
  change (orbGrp Φ K).map (MulAut.conj g).toMonoidHom ≤ _
  rw [orbGrp, Subgroup.map_iSup]
  refine iSup_le fun h => ?_
  change conjSub g (conjSub (h : Q) K) ≤ _
  rw [← conjSub_mul]
  exact conjSub_le_orbGrp K ⟨g * h, (omegaGen Φ).mul_mem hg h.2⟩

theorem conjSub_orbGrp {K : Subgroup Q} {g : Q} (hg : g ∈ omegaGen Φ) :
    conjSub g (orbGrp Φ K) = orbGrp Φ K := by
  refine le_antisymm (conjSub_orbGrp_le hg) ?_
  have h1 := conjSub_mono (n := g) (conjSub_orbGrp_le (K := K) ((omegaGen Φ).inv_mem hg))
  rwa [conjSub_conjSub_inv] at h1

theorem isSubnormal_orbGrp (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ) :
    IsSubnormal (orbGrp Φ K) ⊤ := by
  have hQ₀ := omegaGen_normal hcl
  have hn : ((orbGrp Φ K).subgroupOf (omegaGen Φ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (orbGrp_le hcl hK)).mpr fun g hg =>
      mem_normalizer_iff_conjSub_eq.mpr (conjSub_orbGrp hg)
  have hn' : ((omegaGen Φ).subgroupOf ⊤).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr fun g _ =>
      Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)
  exact IsSubnormal.step (orbGrp_le hcl hK) hn
    (IsSubnormal.step le_top hn' (IsSubnormal.refl _))

theorem isSubnormal_orbGrp' (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ) :
    (orbGrp Φ K).IsSubnormal :=
  CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
    (isSubnormal_orbGrp hcl hK) Subgroup.IsSubnormal.top

theorem conjSub_eq_of_forall_commute {d : Q} {A : Subgroup Q} (h : ∀ a ∈ A, d * a = a * d) :
    conjSub d A = A :=
  Lemma52Proof.conjSub_eq_of_centralizes h

theorem exists_orbGrp_conj (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ)
    (hcomm : ∀ J ∈ Φ, (¬ ∃ g ∈ omegaGen Φ, conjSub g K = J) →
      ∀ h ∈ omegaGen Φ, ∀ a ∈ J, ∀ b ∈ conjSub h K, a * b = b * a)
    {g : Q} (hg : g ∈ omegaGen Φ) : ∃ h ∈ orbGrp Φ K, conjSub g K = conjSub h K := by
  have hXQ := orbGrp_le hcl hK
  let P : Q → Prop := fun x =>
    ∀ h ∈ orbGrp Φ K, ∃ h' ∈ orbGrp Φ K, conjSub x (conjSub h K) = conjSub h' K
  have hgen : ∀ J ∈ Φ, ∀ x ∈ J, P x := by
    intro J hJ x hx h hh
    by_cases hc : ∃ g ∈ omegaGen Φ, conjSub g K = J
    · obtain ⟨g', hg', rfl⟩ := hc
      have hxX : x ∈ orbGrp Φ K := conjSub_le_orbGrp K ⟨g', hg'⟩ hx
      exact ⟨x * h, (orbGrp Φ K).mul_mem hxX hh, (conjSub_mul x h K).symm⟩
    · refine ⟨h, hh, conjSub_eq_of_forall_commute fun b hb => ?_⟩
      exact hcomm J hJ hc h (hXQ hh) x hx b hb
  have hP : P g := by
    have hg' : g ∈ ⨆ L : {L : Subgroup Q // L ∈ Φ}, (L : Subgroup Q) := by
      have e : omegaGen Φ = ⨆ L : {L : Subgroup Q // L ∈ Φ}, (L : Subgroup Q) := by
        unfold omegaGen
        exact iSup_subtype'
      rwa [← e]
    refine Subgroup.iSup_induction (fun L : {L : Subgroup Q // L ∈ Φ} => (L : Subgroup Q))
      (C := P) hg' (fun L x hx => hgen L.1 L.2 x hx) ?_ ?_
    · intro h hh
      exact ⟨h, hh, conjSub_one _⟩
    · intro x y hx hy h hh
      obtain ⟨h₁, hh₁, e₁⟩ := hy h hh
      obtain ⟨h₂, hh₂, e₂⟩ := hx h₁ hh₁
      exact ⟨h₂, hh₂, by rw [conjSub_mul, e₁, e₂]⟩
  obtain ⟨h', hh', e⟩ := hP 1 (orbGrp Φ K).one_mem
  exact ⟨h', hh', by rwa [conjSub_one] at e⟩

theorem orbGrp_eq_iSup (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ)
    (hcomm : ∀ J ∈ Φ, (¬ ∃ g ∈ omegaGen Φ, conjSub g K = J) →
      ∀ h ∈ omegaGen Φ, ∀ a ∈ J, ∀ b ∈ conjSub h K, a * b = b * a) :
    orbGrp Φ K = ⨆ h : ↥(orbGrp Φ K), conjSub (h : Q) K := by
  apply le_antisymm
  · refine iSup_le fun g => ?_
    obtain ⟨h, hh, e⟩ := exists_orbGrp_conj hcl hK hcomm g.2
    rw [e]
    exact le_iSup (fun h : ↥(orbGrp Φ K) => conjSub (h : Q) K) ⟨h, hh⟩
  · exact iSup_le fun h => conjSub_le_orbGrp K ⟨h, orbGrp_le hcl hK h.2⟩

variable [Finite Q] {r n : ℕ}

theorem t4Hyp_omegaGen (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore Q = ⊥) :
    T4Hyp r ↥(omegaGen Φ) (restrictFamily Φ (omegaGen Φ)) := by
  have hR := h.restrict (omegaGen Φ)
  have := omegaGen_normal h.hyp.conjInvariant
  exact
    { hyp := hR.hyp
      twoGroup := hR.twoGroup
      quat := hR.quat
      tight := hR.tight
      noTwins := fun J hJ J' hJ' u hu hu' => (hR.noTwins J hJ J' ⟨hJ', u, hu, hu'⟩).symm
      aEmpty := fun J hJ => aEmpty_of_noTwins hR.hyp hJ (hR.noTwins J hJ)
      odd := oddCore_normal_eq_bot (omegaGen Φ) hO }

theorem commutes_of_not_conj (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K J : Subgroup Q}
    (hK : K ∈ Φ) (hJ : J ∈ Φ) (hnc : ¬ ∃ g ∈ omegaGen Φ, conjSub g K = J) :
    ∀ a ∈ K, ∀ b ∈ J, a * b = b * a := by
  have hKQ := le_omegaGen hK
  have hJQ := le_omegaGen hJ
  have hn' : Nat.card ↥(omegaGen Φ) < n := lt_of_le_of_lt (Subgroup.card_le_card_group _) hn
  have hc := h4 _ hn' _ (t4Hyp_omegaGen h hO) (K.subgroupOf (omegaGen Φ)) ⟨K, hK, hKQ, rfl⟩
    (J.subgroupOf (omegaGen Φ)) ⟨J, hJ, hJQ, rfl⟩ ?_
  · intro a ha b hb
    exact congrArg Subtype.val (hc ⟨a, hKQ ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, hJQ hb⟩
      (Subgroup.mem_subgroupOf.mpr hb))
  · rintro ⟨g, hg⟩
    refine hnc ⟨g, g.2, ?_⟩
    rw [conjSub_subgroupOf, Subgroup.subgroupOf_inj,
      inf_eq_left.mpr (le_omegaGen (h.hyp.conjInvariant _ K hK)), inf_eq_left.mpr hJQ] at hg
    exact hg

theorem le_orbGrp_of_moves (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ)
    {L : Subgroup Q} (hL : IsComponent L) (hm : ∃ y ∈ K, ∃ l ∈ L, y * l ≠ l * y) :
    L ≤ orbGrp Φ K := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hL (isSubnormal_orbGrp' hcl hK) with
    h | h
  · exact h
  · exfalso
    obtain ⟨y, hy, l, hl, hne⟩ := hm
    have hc := Subgroup.commutator_mem_commutator hl (le_orbGrp (Φ := Φ) K hy)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hne hc.symm

omit [Finite Q] in
theorem exists_ne_of_isComponent {L : Subgroup Q} (hL : IsComponent L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, a.2, b, b.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h

theorem commute_conj_of_not_conj (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) : ∀ J ∈ Φ, (¬ ∃ g ∈ omegaGen Φ, conjSub g K = J) →
      ∀ h ∈ omegaGen Φ, ∀ a ∈ J, ∀ b ∈ conjSub h K, a * b = b * a := by
  intro J hJ hnc h' hh' a ha b hb
  refine commutes_of_not_conj h4 h hO hn hJ (h.hyp.conjInvariant h' K hK) ?_ a ha b hb
  rintro ⟨g, hg, e⟩
  exact hnc ⟨g⁻¹ * h', (omegaGen Φ).mul_mem ((omegaGen Φ).inv_mem hg) hh', by
    rw [conjSub_mul, ← e, conjSub_inv_conjSub]⟩

theorem exists_conj_of_moves (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {L : Subgroup Q}
    (hL : IsComponent L) {K J : Subgroup Q} (hK : K ∈ Φ) (hJ : J ∈ Φ)
    (hKm : ∃ y ∈ K, ∃ l ∈ L, y * l ≠ l * y) (hJm : ∃ y ∈ J, ∃ l ∈ L, y * l ≠ l * y) :
    ∃ g ∈ orbGrp Φ K, conjSub g K = J := by
  have hcl := h.hyp.conjInvariant
  by_cases hc : ∃ g ∈ omegaGen Φ, conjSub g K = J
  · obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨h', hh', e⟩ :=
      exists_orbGrp_conj hcl hK (commute_conj_of_not_conj h4 h hO hn hK) hg
    exact ⟨h', hh', e.symm⟩
  · exfalso
    have hXX : orbGrp Φ K ≤ Subgroup.centralizer (orbGrp Φ J : Set Q) := by
      refine iSup_le fun g => ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup_le fun g' => ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      refine commutes_of_not_conj h4 h hO hn (hcl _ K hK) (hcl _ J hJ) ?_ a ha b hb
      rintro ⟨k, hk, e⟩
      refine hc ⟨(g' : Q)⁻¹ * (k * g), (omegaGen Φ).mul_mem ((omegaGen Φ).inv_mem g'.2)
        ((omegaGen Φ).mul_mem hk g.2), ?_⟩
      rw [conjSub_mul, conjSub_mul, e, conjSub_inv_conjSub]
    obtain ⟨a, ha, b, hb, hab⟩ := exists_ne_of_isComponent hL
    have hLK := le_orbGrp_of_moves hcl hK hL hKm
    have hLJ := le_orbGrp_of_moves hcl hJ hL hJm
    exact hab (Subgroup.mem_centralizer_iff.mp (hXX (hLK ha)) b (hLJ hb)).symm

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
