module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P9Defs
import CFSG.Sporadic.Recognition.HeMultiplierCert
import CFSG.Sporadic.Recognition.ONMultiplierCert
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem isElementaryAbelian_center_of_sq {X : Type*} [Group X]
    (h : ∀ z : center X, z ^ 2 = 1) : IsElementaryAbelian 2 (center X) :=
  { toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one h }

private theorem sq_eq_one_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) (g : G) : g ^ 2 = 1 := by
  have h1 : orderOf g ≤ 2 := (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard g)).trans h
  have h2 : 0 < orderOf g := orderOf_pos g
  rcases (show orderOf g = 1 ∨ orderOf g = 2 by omega) with h3 | h3
  · rw [orderOf_eq_one_iff.mp h3, one_pow]
  · rw [← h3, pow_orderOf_eq_one]

private theorem card_eq_four_isCyclic {G : Type*} [Group G] [Finite G]
    (h4 : Nat.card G ∣ 4) {g : G} (hg : g ^ 2 ≠ 1) : Nat.card G = 4 ∧ IsCyclic G := by
  have hdvd : orderOf g ∣ 4 := (orderOf_dvd_natCard g).trans h4
  have hn2 : ¬ orderOf g ∣ 2 := fun h => hg (orderOf_dvd_iff_pow_eq_one.mp h)
  have ho : orderOf g = 4 := by
    obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf g ∣ 2 ^ 2 from hdvd)
    interval_cases i
    · exact absurd (hgi ▸ one_dvd 2) hn2
    · exact absurd (hgi ▸ dvd_refl 2) hn2
    · exact hgi
  have hc : Nat.card G = 4 := Nat.dvd_antisymm h4 (ho ▸ orderOf_dvd_natCard g)
  exact ⟨hc, isCyclic_of_orderOf_eq_card g (ho.trans hc.symm)⟩

private theorem map_fusionZStar_eq_center (P : Type*) [Group P] :
    (Open.fusionZStar P).map (QuotientGroup.mk' (pPrimeCore 2 P)) =
      center (P ⧸ pPrimeCore 2 P) := by
  rw [TBLit.fusionZStar_eq_centralPreimage]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

private theorem card_center_coreQuotient_dvd (P : Type*) [Group P] :
    Nat.card (center (P ⧸ pPrimeCore 2 P)) ∣ Nat.card (Open.fusionZStar P) := by
  rw [← map_fusionZStar_eq_center]
  exact Subgroup.card_map_dvd _ _

private theorem sq_center_coreQuotient {P : Type*} [Group P]
    (h : ∀ z ∈ Open.fusionZStar P, z * z = 1) (c : center (P ⧸ pPrimeCore 2 P)) :
    c ^ 2 = 1 := by
  have hc : (c : P ⧸ pPrimeCore 2 P) ∈ (Open.fusionZStar P).map (QuotientGroup.mk' _) := by
    rw [map_fusionZStar_eq_center]
    exact c.2
  obtain ⟨z, hz, hzc⟩ := hc
  apply Subtype.ext
  rw [pow_two, Subgroup.coe_mul, ← hzc, ← map_mul, h z hz, map_one, Subgroup.coe_one]

theorem l34ExpFourFixedLeaf_of_pumpLeaf
    (h : L34ExpFourPumpLeaf) : L34ExpFourFixedLeaf := by
  intro Q _ _ hQ hZ2 hcat σ hσ P hPF hP hPne hL34 hnEA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnsq : ¬ ∀ c : center (P ⧸ pPrimeCore 2 P), c ^ 2 = 1 := fun hsq =>
    hnEA (isElementaryAbelian_center_of_sq hsq)
  obtain ⟨σ', hσ'2, -, hP'F, hP'⟩ := GrSLit.isPComponent_image_fixed_centralQuotient σ hσ hPF hP
  set π := QuotientGroup.mk' (center Q)
  set P' := P.map π
  have hP'ne : P' ≠ ⊤ := by
    intro htop
    apply hPne
    refine GrSLit.eq_top_of_sup_center_eq_top hQ.1.commutator_eq_top ?_
    rw [eq_top_iff]
    intro y _
    have hy : π y ∈ P' := htop ▸ mem_top _
    obtain ⟨t, ht, hty⟩ := hy
    have hz : t⁻¹ * y ∈ center Q := (QuotientGroup.eq (s := center Q)).mp hty
    have : y = t * (t⁻¹ * y) := by group
    rw [this]
    exact mul_mem (mem_sup_left ht) (mem_sup_right hz)
  let g : P →* P' := (π.comp P.subtype).codRestrict P' fun x => mem_map_of_mem π x.2
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, hy⟩, rfl⟩
  have hgker : ∀ x : P, g x = 1 ↔ (x : Q) ∈ center Q := fun x =>
    ⟨fun h1 => (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1),
      fun h1 => Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)⟩
  have : Group.IsPerfect P := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hP
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPF).toMonoidHom)
      (subgroupOfEquivOfLe hPF).surjective
  obtain ⟨-, -, hPq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P (fixedSubgroup σ) hPF).mp hP
  obtain ⟨-, -, hP'q⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P' (fixedSubgroup σ') hP'F).mp hP'
  have hP'O : pPrimeCore 2 P' ≠ ⊤ := by
    intro htop
    obtain ⟨-, hs, -⟩ := hP'q
    have hsub : Subsingleton (P' ⧸ pPrimeCore 2 P') := QuotientGroup.subsingleton_iff.mpr htop
    have : Nontrivial ((P' ⧸ pPrimeCore 2 P') ⧸ center (P' ⧸ pPrimeCore 2 P')) :=
      hs.toNontrivial
    have : Subsingleton ((P' ⧸ pPrimeCore 2 P') ⧸ center (P' ⧸ pPrimeCore 2 P')) := by
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [Subsingleton.elim x' y']
    exact false_of_nontrivial_of_subsingleton ((P' ⧸ pPrimeCore 2 P') ⧸
      center (P' ⧸ pPrimeCore 2 P'))
  have hcomap := GrSLit.comap_fusionZStar_of_surjective' g hg hPq hP'O
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' g hg hPq hP'O
  have hP'34 : GrSLit.IsL34Type (P' ⧸ Open.fusionZStar P') :=
    Blueprint.LieModel.of_mulEquiv eZ
      (Blueprint.LieModel.of_mulEquiv (TBLit.coreQuotientCenterEquiv P) hL34)
  rcases h (Q ⧸ center Q) hQ.2.1 hQ.2.2 hcat σ' P' ⟨hσ'2, hP'F, hP', hP'ne⟩ hP'34 with
    ⟨⟨eHe⟩, hsq⟩ | ⟨⟨eON⟩, hcard4⟩ | ⟨hbot, hC2⟩
  ·
    exfalso
    have hZ : center Q = ⊥ :=
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate Q hQ ⟨eHe⟩
    refine hnsq (sq_center_coreQuotient fun z hz => ?_)
    rw [← hcomap, mem_comap] at hz
    have h1 : g (z * z) = 1 := by
      rw [map_mul]
      exact hsq _ hz
    have h2 := (hgker _).mp h1
    rw [hZ, mem_bot] at h2
    exact Subtype.ext h2
  ·
    have hZ : center Q = ⊥ :=
      Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate hQ.1 hZ2 eON
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h2 := (hgker x).mp hx
      rw [hZ, mem_bot] at h2
      exact Subtype.ext h2
    have hcardZ : Nat.card (Open.fusionZStar P) = 4 := by
      have e1 := Subgroup.card_map_of_injective (K := (Open.fusionZStar P').comap g) hginj
      rw [map_comap_eq_self_of_surjective hg] at e1
      rw [← hcomap, ← e1, hcard4]
    obtain ⟨c, hc⟩ := not_forall.mp hnsq
    obtain ⟨h4, hcyc⟩ := card_eq_four_isCyclic (hcardZ ▸ card_center_coreQuotient_dvd P) hc
    exact ⟨⟨eON⟩, hcyc, h4⟩
  ·
    exfalso
    have hZQ : Nat.card (center Q) ≤ 2 := by
      have h1 := GrSLit.card_le_of_isPGroup_of_sylow_le (hC2 Q hQ ⟨MulEquiv.refl _⟩)
        (hZ2.to_subgroup ⊤)
      rwa [Subgroup.card_top] at h1
    have hle : ∀ z ∈ Open.fusionZStar P, (z : Q) ∈ center Q := by
      intro z hz
      rw [← hcomap, hbot, mem_comap, mem_bot] at hz
      exact (hgker z).mp hz
    let φ : Open.fusionZStar P → center Q := fun z => ⟨z.1.1, hle z.1 z.2⟩
    have hφ : Function.Injective φ := fun a b hab => by
      have hab' := congrArg (fun w : center Q => (w : Q)) hab
      exact Subtype.ext (Subtype.ext hab')
    have hcardZ : Nat.card (Open.fusionZStar P) ≤ 2 :=
      (Nat.card_le_card_of_injective φ hφ).trans hZQ
    exact hnsq (sq_eq_one_of_card_le_two
      ((Nat.le_of_dvd Nat.card_pos (card_center_coreQuotient_dvd P)).trans hcardZ))

end CFSG.ComponentClassification.GS82PumpInputs
