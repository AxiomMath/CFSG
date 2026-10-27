module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.Lift

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Open Subgroup
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)
open scoped commutatorElement

@[expose] def FixedBlocks (p : ℕ) {P : Type*} [Group P] (α : MulAut P) (r : ℕ) : Prop :=
  ∃ (H : Fin r → Subgroup P) (t : Fin r → P),
    (∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, Commute a b) ∧ (∀ i, ∀ a ∈ H i, α a = a) ∧
      (∀ i, t i ∈ ⁅H i, H i⁆) ∧ (∀ i, t i ^ p = 1) ∧ ∀ i, ∃ h ∈ H i, ¬ Commute (t i) h

variable {p r : ℕ}

theorem FixedBlocks.map {P Q : Type*} [Group P] [Group Q] {α : MulAut P} {β : MulAut Q}
    (e : P →* Q) (he : Function.Injective e) (hβ : ∀ x, β (e x) = e (α x))
    (h : FixedBlocks p α r) : FixedBlocks p β r := by
  obtain ⟨H, t, hcomm, hfix, ht, htp, hnc⟩ := h
  refine ⟨fun i => (H i).map e, fun i => e (t i), ?_, ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hcomm i j hij a ha b hb).map e
  · rintro i _ ⟨a, ha, rfl⟩
    rw [hβ, hfix i a ha]
  · rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem e (ht i)
  · rw [← map_pow, htp i, map_one]
  · obtain ⟨g, hg, hng⟩ := hnc i
    refine ⟨e g, Subgroup.mem_map_of_mem e hg, fun hc => hng ?_⟩
    have hc' : e (t i) * e g = e g * e (t i) := hc
    exact he (by rw [map_mul, map_mul, hc'])

theorem FixedBlocks.conj {P : Type*} [Group P] {α : MulAut P} (ψ : MulAut P)
    (h : FixedBlocks p α r) : FixedBlocks p (ψ * α * ψ⁻¹) r :=
  h.map ψ.toMonoidHom (fun a b hab => ψ.injective hab) fun x => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply_self]

theorem card_closure_eq {P : Type*} [Group P] [Finite P] (hp : p.Prime) (H : Fin r → Subgroup P)
    (t : Fin r → P) (hcomm : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, Commute a b)
    (htH : ∀ i, t i ∈ H i) (htp : ∀ i, t i ^ p = 1) (hnc : ∀ i, ∃ h ∈ H i, ¬ Commute (t i) h) :
    Nat.card (closure (Set.range t)) = p ^ r := by
  haveI := Fact.mk hp
  have hord : ∀ i, orderOf (t i) = p := fun i => orderOf_eq_prime (htp i) fun h1 => by
    obtain ⟨g, -, hg⟩ := hnc i
    exact hg (by rw [h1]; exact Commute.one_left g)
  have hzc : Pairwise fun i j => ∀ x y : P, x ∈ zpowers (t i) → y ∈ zpowers (t j) →
      Commute x y := by
    intro i j hij x y hx hy
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨b, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((hcomm i j hij _ (htH i) _ (htH j)).zpow_left a).zpow_right b
  have hcent : ∀ i, (⨆ (j) (_ : j ≠ i), zpowers (t j)) ≤ centralizer (H i : Set P) :=
    fun i => iSup₂_le fun j hj => zpowers_le.2 (mem_centralizer_iff.2 fun g hg =>
      (hcomm j i hj _ (htH j) g hg).symm.eq)
  have hind : iSupIndep fun i => zpowers (t i) := by
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxi hxo
    by_contra hx1
    have hdvd : orderOf x ∣ p := by
      rw [← hord i]
      exact orderOf_dvd_of_mem_zpowers hxi
    have hxp : orderOf x = p :=
      (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left fun h => hx1 (orderOf_eq_one_iff.1 h)
    have heq : zpowers x = zpowers (t i) := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxi)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxp, hord i])
    have hle := zpowers_le.2 (hcent i hxo)
    rw [heq] at hle
    obtain ⟨g, hg, hng⟩ := hnc i
    exact hng (mem_centralizer_iff.1 (zpowers_le.1 hle) g hg).symm
  have hcl : closure (Set.range t) = ⨆ i, zpowers (t i) := by
    rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
    simp only [zpowers_eq_closure]
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hzc) hind
  have hr : (Subgroup.noncommPiCoprod hzc).range = ⨆ i, zpowers (t i) :=
    Subgroup.noncommPiCoprod_range
  rw [hcl, ← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
  simp [Nat.card_zpowers, hord]

theorem card_range_le_card_ker_powMonoidHom {A Q : Type*} [CommGroup A] [Finite A] [Group Q]
    (g : A →* Q) (hg : ∀ a, g a ^ p = 1) :
    Nat.card g.range ≤ Nat.card (powMonoidHom p : A →* A).ker := by
  have h1 := Subgroup.card_ker_mul_card_range (powMonoidHom p : A →* A)
  have h2 := Subgroup.card_ker_mul_card_range g
  have h3 : Nat.card (powMonoidHom p : A →* A).range ≤ Nat.card g.ker := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hg]
  have h4 : Nat.card g.ker * Nat.card g.range ≤
      Nat.card g.ker * Nat.card (powMonoidHom p : A →* A).ker :=
    calc Nat.card g.ker * Nat.card g.range
        = Nat.card (powMonoidHom p : A →* A).ker * Nat.card (powMonoidHom p : A →* A).range := by
          rw [h1, h2]
      _ ≤ Nat.card (powMonoidHom p : A →* A).ker * Nat.card g.ker := Nat.mul_le_mul_left _ h3
      _ = Nat.card g.ker * Nat.card (powMonoidHom p : A →* A).ker := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h4 Nat.card_pos

theorem exists_elemAbelian_fixed_of_hom {L Q : Type*} [Group L] [Finite L] [Group Q]
    (hp : p.Prime) (π : L →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ center L)
    {α : MulAut L} {β : MulAut Q} (hαβ : ∀ x, π (α x) = β (π x)) (h : FixedBlocks p β r) :
    ∃ F : Subgroup L, IsElemAbelian p F ∧ p ^ r ≤ Nat.card F ∧ ∀ x ∈ F, α x = x := by
  classical
  haveI : Finite Q := Finite.of_surjective π hπ
  obtain ⟨Hb, tb, hcomm, hfix, ht, htp, hnc⟩ := h
  have hαZ : ∀ i, ∀ w ∈ (Hb i).comap π, α w * w⁻¹ ∈ center L := fun i w hw => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hfix i _ (Subgroup.mem_comap.1 hw),
      mul_inv_cancel])
  have hfixc : ∀ i, ∀ c ∈ ⁅(Hb i).comap π, (Hb i).comap π⁆, α c = c := fun i =>
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.fixed_of_mem_commutator α _ (hαZ i)
  have hcent : ∀ i j, i ≠ j → ∀ c ∈ ⁅(Hb i).comap π, (Hb i).comap π⁆, ∀ g ∈ (Hb j).comap π,
      g * c * g⁻¹ = c := by
    intro i j hij c hc g hg
    have hgZ : ∀ w ∈ (Hb i).comap π, MulAut.conj g w * w⁻¹ ∈ center L := fun w hw => hker (by
      have hc' : π w * π g = π g * π w :=
        hcomm i j hij _ (Subgroup.mem_comap.1 hw) _ (Subgroup.mem_comap.1 hg)
      rw [MulAut.conj_apply, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [← hc']
      group)
    simpa only [MulAut.conj_apply] using
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.fixed_of_mem_commutator (MulAut.conj g) _
        hgZ c hc
  have hlift : ∀ i, ∃ s ∈ ⁅(Hb i).comap π, (Hb i).comap π⁆, π s = tb i := fun i =>
    Subgroup.mem_map.1 (by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ]
      exact ht i)
  choose s hs hst using hlift
  have hscomm : (Set.range s).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (by rw [h])
    exact (mul_inv_eq_iff_eq_mul.1 (hcent i j hij _ (hs i) _
      (Subgroup.commutator_le_self _ (hs j)))).symm
  have hAcomm : ∀ a b : ↥(closure (Set.range s)), a * b = b * a := by
    haveI := isMulCommutative_closure hscomm
    exact fun a b => mul_comm' a b
  letI : CommGroup ↥(closure (Set.range s)) :=
    { (inferInstance : Group ↥(closure (Set.range s))) with mul_comm := hAcomm }
  have hAfix : closure (Set.range s) ≤ MonoidHom.eqLocus (α : L →* L) (MonoidHom.id L) :=
    (closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact hfixc i (s i) (hs i))
  have himage : (closure (Set.range s)).map π = closure (Set.range tb) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    exact congrArg (fun S => Subgroup.closure (Set.range S)) (funext hst)
  have hcard : Nat.card (closure (Set.range tb)) = p ^ r :=
    card_closure_eq hp Hb tb hcomm (fun i => Subgroup.commutator_le_self _ (ht i)) htp hnc
  have htbcomm : (Set.range tb).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (by rw [h])
    exact hcomm i j hij _ (Subgroup.commutator_le_self _ (ht i)) _
      (Subgroup.commutator_le_self _ (ht j))
  have hexp : ∀ x ∈ closure (Set.range tb), x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := ha
        exact htp i
    | one => exact one_pow p
    | mul a b ha hb iha ihb =>
        have hab : Commute a b := by
          haveI := isMulCommutative_closure htbcomm
          exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : closure (Set.range tb)) ⟨b, hb⟩)
        rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hcount := card_range_le_card_ker_powMonoidHom (π.comp (closure (Set.range s)).subtype)
    (fun a => hexp _ (by
      rw [← himage]
      exact Subgroup.mem_map_of_mem π a.2))
  rw [MonoidHom.range_comp, Subgroup.range_subtype, himage, hcard] at hcount
  refine ⟨(powMonoidHom p : ↥(closure (Set.range s)) →* _).ker.map (closure (Set.range s)).subtype,
    ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩,
    ?_, ?_⟩
  · apply Subtype.ext
    obtain ⟨a', -, ha'⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', -, hb'⟩ := Subgroup.mem_map.1 b.2
    change (a : L) * b = b * a
    rw [← ha', ← hb']
    exact congrArg Subtype.val (hAcomm a' b')
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
  · rw [Subgroup.card_map_of_injective (closure (Set.range s)).subtype_injective]
    exact hcount
  · rintro _ ⟨a, -, rfl⟩
    exact hAfix a.2

theorem le_pRank_of_fixedBlocks {X : Type*} [Group X] [Finite X] (hp : p.Prime) (K : Subgroup X)
    {y : X} (hy : y ∈ normalizer (K : Set X))
    (h : FixedBlocks p (onCenterQuotient (K.normalizerMonoidHom ⟨y, hy⟩)) r) :
    r ≤ pRank p (K ⊓ centralizer {y}) := by
  haveI := Fact.mk hp
  obtain ⟨F, hF, hcard, hfix⟩ := exists_elemAbelian_fixed_of_hom hp
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (fun x => (onCenterQuotient_apply_mk _ x).symm) h
  have hF' : IsElemAbelian p (F.map K.subtype) := CFSG.SectionRank.isElemAbelian_map hF K.subtype
  have hpg : IsPGroup p (F.map K.subtype) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hF'.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  have hrk : r ≤ k := by
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hk
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  refine hrk.trans (CFSG.SectionRank.le_pRank hp.one_lt ?_ hF' hk)
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_inf.2 ⟨x.2, mem_centralizer_iff.2 fun z hz => ?_⟩
  rw [Set.mem_singleton_iff.1 hz]
  have h1 := congrArg Subtype.val (hfix x hx)
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  change y * x * y⁻¹ = x at h1
  change y * x = x * y
  calc y * (x : X) = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [h1]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
