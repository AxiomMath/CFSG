module

public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralKernel
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

section Chains

variable {G G' : Type*} [Group G] [Group G']

theorem assembly_isSubnormal_map (f : G →* G') {H K : Subgroup G}
    (h : CFSG.Assembly.IsSubnormal H K) : CFSG.Assembly.IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem assembly_isSubnormal_comap (f : G →* G') {H K : Subgroup G'}
    (h : CFSG.Assembly.IsSubnormal H K) : CFSG.Assembly.IsSubnormal (H.comap f) (K.comap f) :=
  h.comap f

theorem ne_bot_of_isComponentOf {Q H : Subgroup G} (hQ : CFSG.Assembly.IsComponentOf Q H) :
    Q ≠ ⊥ := by
  intro h
  apply not_le_centralizer_self_of_isQuasisimple hQ.2.2
  rw [h]
  exact bot_le

theorem layer_map_subtype (H : Subgroup G) :
    (layer H).map H.subtype = sSup {Q : Subgroup G | CFSG.Assembly.IsComponentOf Q H} := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    show sSup {K : Subgroup H | CFSG.IsComponent K} ≤ _
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap]
    refine le_sSup ?_
    show CFSG.Assembly.IsComponentOf (K.map H.subtype) H
    rw [isComponentOf_iff_isComponent_subgroupOf (map_subtype_le K)]
    have hKK : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
    rw [hKK]
    exact hK
  · refine sSup_le fun Q hQ => ?_
    have hK : CFSG.IsComponent (Q.subgroupOf H) :=
      (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
    have hQeq : Q = (Q.subgroupOf H).map H.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQ.1]
    rw [hQeq]
    exact map_mono (le_sSup hK)

theorem layer_eq_bot_iff (H : Subgroup G) :
    layer H = ⊥ ↔ {Q : Subgroup G | CFSG.Assembly.IsComponentOf Q H} = ∅ := by
  rw [← Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective, layer_map_subtype,
    sSup_eq_bot, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h Q hQ => ne_bot_of_isComponentOf hQ (h Q hQ), fun h Q hQ => absurd hQ (h Q)⟩

end Chains

theorem center_quotient_equiv_of_surjective {Q R : Type*} [Group Q] [Group R]
    (hQ : CFSG.IsQuasisimple Q) (f : Q →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) : Nonempty (Q ⧸ center Q ≃* R ⧸ center R) := by
  obtain ⟨-, -, hcen⟩ := quasisimple_central_quotient hQ hker
  let e1 : Q ⧸ f.ker ≃* R := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e2 : R ⧸ center R ≃* (Q ⧸ f.ker) ⧸ center (Q ⧸ f.ker) :=
    QuotientGroup.congr (center R) (center (Q ⧸ f.ker)) e1.symm (Subgroup.map_center_eq e1.symm)
  exact ⟨(e2.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hker))).symm⟩

theorem commutator_self_of_commutator_eq_top {G : Type*} [Group G] {L : Subgroup G}
    (h : commutator L = ⊤) : ⁅L, L⁆ = L := by
  have h' := congrArg (Subgroup.map L.subtype) h
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h'

section Correspondence

variable {P S : Type*} [Group P] [Group S] {π : P →* S} {a : MulAut P} {α : MulAut S}

theorem map_fixed_le (hcomm : ∀ x, π (a x) = α (π x)) :
    (fixedSubgroup a).map π ≤ fixedSubgroup α := by
  rintro _ ⟨x, hx, rfl⟩
  change α (π x) = π x
  rw [← hcomm, show a x = x from hx]

theorem commutator_fixed_le_image [Finite P] (hπ : Function.Surjective π)
    (hK : π.ker ≤ center P) (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x)) :
    ⁅fixedSubgroup α, fixedSubgroup α⁆ ≤ (fixedSubgroup a).map π := by
  obtain ⟨hN, -, hab⟩ := fixedImage_quotient_embedding hK hπ ha hcomm
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (QuotientGroup.mk' (((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)))
      ⁅(⟨x, hx⟩ : fixedSubgroup α), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab.toIsMulCommutative.is_comm.comm _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem isComponentOf_map_fixed [Finite P] (hπ : Function.Surjective π)
    (hK : π.ker ≤ center P) (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    {Q : Subgroup P} (hQ : CFSG.Assembly.IsComponentOf Q (fixedSubgroup a)) :
    CFSG.Assembly.IsComponentOf (Q.map π) (fixedSubgroup α) := by
  have hIC := map_fixed_le hcomm
  have hN := fixedImage_normal hK hπ ha hcomm
  refine ⟨(map_mono hQ.1).trans hIC, ?_, ?_⟩
  · exact assembly_isSubnormal_trans (assembly_isSubnormal_map π hQ.2.1)
      (CFSG.Assembly.IsSubnormal.step hIC hN (CFSG.Assembly.IsSubnormal.refl _))
  · have hQn := (AssemblyBPredicates.isQuasisimple_iff_native Q).1 hQ.2.2
    rcases quasisimple_homomorphic_images hQn (π.comp Q.subtype) with h | h
    · exfalso
      apply not_le_centralizer_self_of_isQuasisimple hQ.2.2
      have hQK : Q ≤ π.ker := by
        intro x hx
        have hmem : π.comp Q.subtype ⟨x, hx⟩ ∈ (π.comp Q.subtype).range := ⟨_, rfl⟩
        rw [h, mem_bot] at hmem
        exact hmem
      intro x hx
      rw [mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.1 (hK (hQK hx)) y
    · have hrange : (π.comp Q.subtype).range = Q.map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange] at h
      exact (AssemblyBPredicates.isQuasisimple_iff_native _).2 h

theorem lift_isComponentOf_fixed [Finite P] (hπ : Function.Surjective π)
    (hK : π.ker ≤ center P) (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    {R : Subgroup S} (hR : CFSG.Assembly.IsComponentOf R (fixedSubgroup α)) :
    ⁅R.comap π, R.comap π⁆ = ⁅fixedSubgroup a ⊓ R.comap π, fixedSubgroup a ⊓ R.comap π⁆ ∧
      CFSG.Assembly.IsComponentOf ⁅R.comap π, R.comap π⁆ (fixedSubgroup a) ∧
      ⁅R.comap π, R.comap π⁆.map π = R ∧ ∀ x ∈ ⁅R.comap π, R.comap π⁆, a x = x := by
  set B := fixedSubgroup a
  set C := fixedSubgroup α
  set D := R.comap π with hD
  have hRR : ⁅R, R⁆ = R := commutator_self_of_isQuasisimple hR.2.2
  have hRI : R ≤ B.map π := by
    calc R = ⁅R, R⁆ := hRR.symm
      _ ≤ ⁅C, C⁆ := commutator_mono hR.1 hR.1
      _ ≤ B.map π := commutator_fixed_le_image hπ hK ha hcomm
  have hperfR : Group.IsPerfect R := ⟨hR.2.2.1⟩
  have hRfix : ∀ s ∈ R, α s = s := fun s hs => hR.1 hs
  obtain ⟨hQperf, hQmap, hQfix⟩ := fixedPerfectLift hπ hK hcomm R hRfix
  have hQB : ⁅D, D⁆ ≤ B := fun x hx => hQfix x hx
  have hQD : ⁅D, D⁆ ≤ D := Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hQV : ⁅D, D⁆ ≤ B ⊓ D := le_inf hQB hQD
  have hQQ : ⁅⁅D, D⁆, ⁅D, D⁆⁆ = ⁅D, D⁆ := commutator_self_of_commutator_eq_top hQperf.1
  have hVV : ⁅B ⊓ D, B ⊓ D⁆ = ⁅D, D⁆ := le_antisymm
    (commutator_mono inf_le_right inf_le_right)
    (calc ⁅D, D⁆ = ⁅⁅D, D⁆, ⁅D, D⁆⁆ := hQQ.symm
      _ ≤ ⁅B ⊓ D, B ⊓ D⁆ := commutator_mono hQV hQV)
  refine ⟨hVV.symm, ⟨hQB, ?_, ?_⟩, hQmap, hQfix⟩
  · have hnorm : (⁅D, D⁆.subgroupOf (B ⊓ D)).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer hQV, ← hVV]
      exact Subgroup.normalizer_commutator_ge_left _ _
    have hRI' : CFSG.Assembly.IsSubnormal R (B.map π) :=
      (isComponentOf_of_le hR hRI (map_fixed_le hcomm)).2.1
    have hV : CFSG.Assembly.IsSubnormal (B ⊓ D) B := by
      have h2 := assembly_isSubnormal_inf (assembly_isSubnormal_comap π hRI') B
      rw [inf_eq_right.2 (le_comap_map π B), inf_comm] at h2
      exact h2
    exact CFSG.Assembly.IsSubnormal.step hQV hnorm hV
  · let f : D →* R := (π.comp D.subtype).codRestrict R fun x => x.2
    have hf : Function.Surjective f := fun r => by
      obtain ⟨x, hx⟩ := hπ r
      exact ⟨⟨x, show π x ∈ R by rw [hx]; exact r.2⟩, Subtype.ext hx⟩
    have hfker : f.ker ≤ center D := fun x hx => by
      rw [Subgroup.mem_center_iff]
      intro y
      have hxK : (x : P) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : ((f x : R) : S) = 1 := by rw [MonoidHom.mem_ker.1 hx]; rfl
        exact h1
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hK hxK) y)
    have hDq := CentralExtensions.derived_quasisimple hR.2.2 f hf hfker
    have hmapD : (commutator D).map D.subtype = ⁅D, D⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let e : commutator D ≃* (commutator D).map D.subtype :=
      (commutator D).equivMapOfInjective _ D.subtype_injective
    rw [AssemblyBPredicates.isQuasisimple_iff_native, ← hmapD]
    exact (isQuasisimple_congr e).1 ((AssemblyBPredicates.isQuasisimple_iff_native _).1 hDq)

theorem commutator_comap_map_eq (hK : π.ker ≤ center P) {Q : Subgroup P}
    (hQ : CFSG.Assembly.IsQuasisimple Q) : ⁅(Q.map π).comap π, (Q.map π).comap π⁆ = Q := by
  rw [Subgroup.comap_map_eq, CentralExtensions.commutator_sup_central Q π.ker hK,
    commutator_self_of_isQuasisimple hQ]

end Correspondence

theorem full_central_kernel_involution_fixed_component_correspondence {P S : Type*} [Group P]
    [Group S] [Finite P] {π : P →* S} (hπ : Function.Surjective π) (hK : π.ker ≤ center P)
    {a : MulAut P} {α : MulAut S} (ha : ∀ x, a (a x) = x) (_hα : ∀ s, α (α s) = s)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    let B := fixedSubgroup a
    let C := fixedSubgroup α
    let I := B.map π
    (∃ _ : (I.subgroupOf C).Normal, IsElementaryAbelian 2 (C ⧸ I.subgroupOf C) ∧
        ∃ n : ℕ, Nat.card (C ⧸ I.subgroupOf C) = 2 ^ n) ∧
      (π.comp B.subtype).ker = (π.ker ⊓ B).subgroupOf B ∧
      Set.BijOn (Subgroup.map π) {Q | CFSG.Assembly.IsComponentOf Q B}
        {R | CFSG.Assembly.IsComponentOf R C} ∧
      (∀ R : Subgroup S, CFSG.Assembly.IsComponentOf R C →
        let Q := ⁅R.comap π, R.comap π⁆
        Q = ⁅B ⊓ R.comap π, B ⊓ R.comap π⁆ ∧ CFSG.Assembly.IsComponentOf Q B ∧
        Q.map π = R ∧ (∀ x ∈ Q, a x = x) ∧ (π.comp Q.subtype).ker = π.ker.subgroupOf Q ∧
        π.ker.subgroupOf Q ≤ center Q ∧ Nonempty (Q ⧸ center Q ≃* R ⧸ center R)) ∧
      (∀ Q : Subgroup P, CFSG.Assembly.IsComponentOf Q B →
        ⁅(Q.map π).comap π, (Q.map π).comap π⁆ = Q) ∧
      ((layer B).map B.subtype).map π = (layer C).map C.subtype ∧
      (π.comp ((layer B).map B.subtype).subtype).ker =
        π.ker.subgroupOf ((layer B).map B.subtype) ∧
      (layer B = ⊥ ↔ layer C = ⊥) := by
  intro B C I
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_surjective π hπ
  have hquot : ∃ _ : (I.subgroupOf C).Normal, IsElementaryAbelian 2 (C ⧸ I.subgroupOf C) ∧
      ∃ n : ℕ, Nat.card (C ⧸ I.subgroupOf C) = 2 ^ n := by
    obtain ⟨hN, -, hab⟩ := fixedImage_quotient_embedding hK hπ ha hcomm
    refine ⟨hN, hab, IsPGroup.iff_card.1 fun g => ⟨1, ?_⟩⟩
    obtain ⟨k, hk⟩ := hab.exponent_dvd_p
    rw [pow_one, show (2 : ℕ) = Monoid.exponent _ * k from hk, pow_mul,
      Monoid.pow_exponent_eq_one, one_pow]
  have hkerB : (π.comp B.subtype).ker = (π.ker ⊓ B).subgroupOf B := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hbij : Set.BijOn (Subgroup.map π) {Q | CFSG.Assembly.IsComponentOf Q B}
      {R | CFSG.Assembly.IsComponentOf R C} := by
    refine ⟨fun Q hQ => isComponentOf_map_fixed hπ hK ha hcomm hQ, ?_, ?_⟩
    · intro Q₁ hQ₁ Q₂ hQ₂ h
      rw [← commutator_comap_map_eq hK hQ₁.2.2, ← commutator_comap_map_eq hK hQ₂.2.2]
      rw [h]
    · intro R hR
      obtain ⟨-, hQ, hQmap, -⟩ := lift_isComponentOf_fixed hπ hK ha hcomm hR
      exact ⟨_, hQ, hQmap⟩
  have hlift : ∀ R : Subgroup S, CFSG.Assembly.IsComponentOf R C →
      let Q := ⁅R.comap π, R.comap π⁆
      Q = ⁅B ⊓ R.comap π, B ⊓ R.comap π⁆ ∧ CFSG.Assembly.IsComponentOf Q B ∧
      Q.map π = R ∧ (∀ x ∈ Q, a x = x) ∧ (π.comp Q.subtype).ker = π.ker.subgroupOf Q ∧
      π.ker.subgroupOf Q ≤ center Q ∧ Nonempty (Q ⧸ center Q ≃* R ⧸ center R) := by
    intro R hR Q
    obtain ⟨hV, hQ, hQmap, hQfix⟩ := lift_isComponentOf_fixed hπ hK ha hcomm hR
    have hcen : π.ker.subgroupOf Q ≤ center Q := fun x hx => by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hK hx) y)
    let f : Q →* R := (π.comp Q.subtype).codRestrict R fun x => by
      rw [← hQmap]; exact ⟨x, x.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨r, hr⟩
      rw [← hQmap] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfker : f.ker ≤ center Q := fun x hx => hcen (by
      change π x = 1
      have h1 : ((f x : R) : S) = 1 := by rw [MonoidHom.mem_ker.1 hx]; rfl
      exact h1)
    have hQn := (AssemblyBPredicates.isQuasisimple_iff_native Q).1 hQ.2.2
    exact ⟨hV, hQ, hQmap, hQfix, rfl, hcen, center_quotient_equiv_of_surjective hQn f hf hfker⟩
  have hrec : ∀ Q : Subgroup P, CFSG.Assembly.IsComponentOf Q B →
      ⁅(Q.map π).comap π, (Q.map π).comap π⁆ = Q := fun Q hQ =>
    commutator_comap_map_eq hK hQ.2.2
  have hlayer : ((layer B).map B.subtype).map π = (layer C).map C.subtype := by
    rw [layer_map_subtype, layer_map_subtype, (Subgroup.gc_map_comap π).l_sSup, ← hbij.image_eq,
      sSup_image]
  have hiff : layer B = ⊥ ↔ layer C = ⊥ := by
    rw [layer_eq_bot_iff, layer_eq_bot_iff, ← hbij.image_eq, Set.image_eq_empty]
  exact ⟨hquot, hkerB, hbij, hlift, hrec, hlayer, rfl, hiff⟩

end CFSG.LocalAnalysis.ComponentInitial
