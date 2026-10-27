module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped commutatorElement

theorem commutator_eq_self_or_eq_bot_of_le_normalizer {G : Type*} [Group G] {H T : Subgroup G}
    (hT : T ≤ normalizer (H : Set G)) (hH : IsQuasisimple ↥H) : ⁅H, T⁆ = H ∨ ⁅H, T⁆ = ⊥ := by
  have hNH : ⁅H, T⁆ ≤ H := by
    rw [commutator_le]
    intro h hh t ht
    rw [commutatorElement_def, show h * t * h⁻¹ * t⁻¹ = h * (t * h⁻¹ * t⁻¹) by group]
    exact H.mul_mem hh ((mem_normalizer_iff.mp (hT ht) h⁻¹).mp (H.inv_mem hh))
  have hnorm : (⁅H, T⁆.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (normalizer_commutator_ge_left H T)
  rcases LocalCores.quasisimple_normal_subgroups hH hnorm with htop | hcen
  · left
    refine le_antisymm hNH fun x hx => ?_
    have : (⟨x, hx⟩ : ↥H) ∈ ⁅H, T⁆.subgroupOf H := by rw [htop]; exact mem_top _
    exact this
  · right
    have hNC : ⁅H, T⁆ ≤ centralizer (H : Set G) := fun x hx =>
      mem_centralizer_iff.mpr fun y hy => by
        have := mem_center_iff.mp (hcen (show (⟨x, hNH hx⟩ : ↥H) ∈ ⁅H, T⁆.subgroupOf H from hx))
          ⟨y, hy⟩
        exact congrArg Subtype.val this
    have h1 : ⁅⁅H, T⁆, H⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hNC
    have h2 : ⁅⁅T, H⁆, H⁆ = ⊥ := by rw [commutator_comm T H]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    have : Group.IsPerfect ↥H := hH.1
    rwa [commutator_eq_self] at h3

theorem le_layerIn_of_isComponent {G : Type*} [Group G] [Finite G] (hG : pPrimeCore 2 G = ⊥)
    {J A : Subgroup G} (hJ : IsComponent J) (hJA : J ≤ A) : J ≤ GSThmB.layerIn A := by
  have h2 : IsTwoComponent J := (isTwoComponent_iff_isComponent hG J).mpr hJ
  have h3 : IsTwoComponentIn J A :=
    ⟨hJA, GorensteinWalter.isSubnormal_subgroupOf_of_subnormal_of_le hJA h2.1, h2.2⟩
  have h4 := (isTwoComponentIn_iff hJA).mp h3
  intro x hx
  exact ⟨⟨x, hJA hx⟩, (le_sSup (s := {L : Subgroup ↥A | IsPComponent 2 L}) h4 :
    _ ≤ pLayer ↥A 2) (show (⟨x, hJA hx⟩ : ↥A) ∈ J.subgroupOf A from hx), rfl⟩

theorem eq_bot_of_isPerfect_of_isPGroup_quotient {C : Type*} [Group C] [Finite C]
    (hC : IsPGroup 2 (C ⧸ pPrimeCore 2 C)) {J : Subgroup C} (hJ : Group.IsPerfect ↥J) :
    J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have himg : J.map (QuotientGroup.mk' (pPrimeCore 2 C)) = ⊥ := by
    have hperf : Group.IsPerfect ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 C))) :=
      Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' (pPrimeCore 2 C)).subgroupMap J)
        ((QuotientGroup.mk' (pPrimeCore 2 C)).subgroupMap_surjective J)
    have h2 : IsPGroup 2 ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 C))) := hC.to_subgroup _
    have : Group.IsNilpotent ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 C))) := h2.isNilpotent
    by_contra hne
    have : Nontrivial ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 C))) :=
      (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 C)))
      inferInstance
  have hJO : J ≤ pPrimeCore 2 C := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 C), ← Subgroup.map_eq_bot_iff]
    exact himg
  have hodd : Odd (Nat.card J) :=
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right (card_dvd_of_le hJO)
      (pPrimeCore_coprime_card (p := 2) (G := C)))
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hne
  have : Nontrivial ↥J := (nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem isPGroup_quotient_of_hasDihedralSylowTwo {C : Type} [Group C] [Finite C]
    (hD : GorensteinWalter.HasDihedralSylowTwo C) {b : C} (hb : b ∈ center C)
    (hb2 : orderOf b = 2) : IsPGroup 2 (C ⧸ pPrimeCore 2 C) := by
  set Q := C ⧸ pPrimeCore 2 C
  set bb : Q := QuotientGroup.mk b with hbb
  have hbbc : bb ∈ center Q := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hbb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hb g]
  have hbb1 : bb ≠ 1 := by
    intro h1
    rw [hbb, QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard _ h1
    rw [hb2] at hdvd
    exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)
  have hb2' : b ^ 2 = 1 := by
    rw [← hb2]
    exact pow_orderOf_eq_one b
  have hbb2 : bb ^ 2 = 1 := by
    rw [hbb, ← QuotientGroup.mk_pow, hb2', QuotientGroup.mk_one]
  rcases GorensteinWalter.gorensteinWalter C hD with ⟨-, h⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨-, K, -, L, hLn, hLidx, hLmodel⟩
  · exact h
  · exfalso
    have hcen : center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    apply hbb1
    have h1 : e bb ∈ center (alternatingGroup (Fin 7)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hbbc g]
    rw [hcen, mem_bot] at h1
    exact e.injective (h1.trans (map_one e).symm)
  · exfalso
    have hbL : bb ∈ L := by
      rw [← QuotientGroup.eq_one_iff (N := L)]
      have h1 := orderOf_dvd_natCard (QuotientGroup.mk bb : Q ⧸ L)
      have h2 : orderOf (QuotientGroup.mk bb : Q ⧸ L) ∣ 2 := orderOf_dvd_of_pow_eq_one
        (by rw [← QuotientGroup.mk_pow, hbb2, QuotientGroup.mk_one])
      have h3 : Nat.Coprime 2 (Nat.card (Q ⧸ L)) := Nat.coprime_two_left.mpr hLidx
      have h4 := Nat.eq_one_of_dvd_coprimes h3 h2 h1
      exact orderOf_eq_one_iff.mp h4
    have hcL : (⟨bb, hbL⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp hbbc g)
    apply hbb1
    have hne : (⟨bb, hbL⟩ : ↥L) = 1 := by
      rcases hLmodel with hP | hP
      · obtain ⟨e⟩ := hP
        have h1 : e ⟨bb, hbL⟩ ∈ center (GorensteinWalter.PSL2 K) := by
          rw [mem_center_iff]
          intro g
          obtain ⟨g, rfl⟩ := e.surjective g
          rw [← map_mul, ← map_mul, mem_center_iff.mp hcL g]
        rw [GorensteinWalter.psl2_center_eq_bot, mem_bot] at h1
        exact e.injective (h1.trans (map_one e).symm)
      · obtain ⟨e⟩ := hP
        have h1 : e ⟨bb, hbL⟩ ∈ center (GorensteinWalter.PGL2 K) := by
          rw [mem_center_iff]
          intro g
          obtain ⟨g, rfl⟩ := e.surjective g
          rw [← map_mul, ← map_mul, mem_center_iff.mp hcL g]
        rw [GorensteinWalter.pgl2_center_eq_bot, mem_bot] at h1
        exact e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val hne

end CFSG.ComponentClassification.HarrisLit
