module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Non
public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMax
public import Certificates.Certificate23400
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Equiv

theorem a7_e9_check (π : Perm (Fin 7)) (hπ : π * π = 1)
    (hπ1 : π ≠ 1) (g h : Perm (Fin 7)) (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1) (hgπ : g * π = π * g)
    (hhπ : h * π = π * h) (hg1 : g ≠ 1) (hgh : g * h = h * g) : h = 1 ∨ h = g ∨ h = g * g := by
  have hmem : ∀ x : Perm (Fin 7), x ^ 3 = 1 → x * π = π * x → x ∈ A7Data.cubeCent π := by
    intro x hx3 hxπ
    rw [A7Data.cubeCent, Finset.mem_filter, A7Data.cubes, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, hx3⟩, hxπ⟩
  exact Certificates.certificate23400 π hπ hπ1 g (hmem g hg3 hgπ) h (hmem h hh3 hhπ) hg1
    hgh

theorem card_eq_nine_of_noncyclic {G : Type*} [Group G] [Finite G] (h27 : ¬ 27 ∣ Nat.card G)
    {P : Subgroup G} (hP : IsPGroup 3 P) (hc : ¬ IsCyclic P) : Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card P
  have hk2 : k ≤ 2 := by
    by_contra h
    exact h27 (by simpa using (pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd)
  interval_cases k
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact absurd (inferInstance : IsCyclic P) hc
  · exact absurd (isCyclic_of_prime_card (p := 3) (by simpa using hk)) hc
  · simpa using hk

theorem exists_pair_of_card_nine {G : Type*} [Group G] {P : Subgroup G} (hP9 : Nat.card P = 9)
    (hc : ¬ IsCyclic P) : ∃ g ∈ P, ∃ h ∈ P, g ≠ 1 ∧ g ^ 3 = 1 ∧ h ^ 3 = 1 ∧ g * h = h * g ∧
      h ∉ zpowers g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP9]; norm_num)
  have hexp : ∀ x : P, x ^ 3 = 1 := by
    intro x
    have h9 : orderOf x ∣ 9 := hP9 ▸ orderOf_dvd_natCard x
    have h9' : orderOf x ∣ 3 ^ 2 := by norm_num; exact h9
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9'
    have hi2 : i ≠ 2 := by
      rintro rfl
      exact hc (isCyclic_of_orderOf_eq_card x (by rw [hio, hP9]; norm_num))
    rw [← orderOf_dvd_iff_pow_eq_one, hio]
    exact (pow_dvd_pow 3 (by omega : i ≤ 1)).trans (by norm_num)
  have hcomm : ∀ a b : P, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P)
      (by rw [hP9]; norm_num)).is_comm.comm a b
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hP9]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : P)
  by_cases hall : ∀ y ∈ P, y ∈ zpowers (x : G)
  · refine (hc ⟨⟨x, fun y => ?_⟩⟩).elim
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hall y y.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · push Not at hall
    obtain ⟨y, hy, hyx⟩ := hall
    refine ⟨x, x.2, y, hy, fun h => hx (Subtype.ext h), ?_, ?_, ?_, hyx⟩
    · simpa using congrArg Subtype.val (hexp x)
    · simpa using congrArg Subtype.val (hexp ⟨y, hy⟩)
    · simpa using congrArg Subtype.val (hcomm x ⟨y, hy⟩)

theorem card_of_base {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : Blueprint.LieModel X .PSL 2 3 n) : 27 ∣ Nat.card X ∨ Nat.card X = 360 := by
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num) hF]
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    norm_num
  · exact Or.inl (Dvd.dvd.mul_right ((show (27 : ℕ) = 3 ^ 3 by norm_num) ▸ pow_dvd_pow 3 h3) _)

theorem apply_apply_of_orderOf {X : Type} [Group X] {α : MulAut X} (hα : orderOf α = 2) (x : X) :
    α (α x) = x := by
  have h : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
  exact congrArg (fun β : MulAut X => β x) h

theorem fixedPoints_ne_top {X : Type} [Group X] {α : MulAut X} (hα : orderOf α = 2) :
    fixedPoints α ≠ ⊤ := by
  intro htop
  have h1 : α = 1 := MulEquiv.ext fun x => by
    have hx : x ∈ fixedPoints α := htop ▸ mem_top x
    exact mem_fixedPoints.mp hx
  rw [h1, orderOf_one] at hα
  exact absurd hα (by norm_num)

theorem not_harrisF_L34
    {X : Type} [Group X] (hX : Blueprint.LieModel X .PSL 3 2 2) : ¬ HarrisF 3 X := by
  intro hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hk4 : Nat.card k = 4 := by rw [hk]; norm_num
  have hcard : Nat.card X = 20160 := by
    rw [Nat.card_congr e.toEquiv, RankThree.PartTwo.KFacts.L34.card_projectiveSL hk4]
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨e1⟩ := GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := GH74.KGroups.GF4) 3 2 2
    (by norm_num) GH74.KGroups.L34.card_F hX
  obtain ⟨e2⟩ := GH74.KGroups.L34.equiv_psl_P21
  rcases harrisF_cases hF with ⟨n, hn, hm⟩ | ⟨α, hα, h360, E, hEα, hE, hc⟩
  · rcases card_of_base hn hm with h | h <;> rw [hcard] at h <;> norm_num at h
  have hE9 : Nat.card E = 9 := card_eq_nine_of_noncyclic (by rw [hcard]; norm_num) hE hc
  have hcent : ∀ t ∈ E, t ≠ 1 → ∀ g : X, g * t = t * g → g ∈ E := by
    intro t ht ht1 g hg
    have hE' : Nat.card (E.map e.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective e.injective, hE9]
    have h1 := RankThree.PartTwo.KFacts.L34.centralizer_eq_of_card_eq_nine hk4 hE'
      (mem_map_of_mem e.toMonoidHom ht) (fun h => ht1 (e.map_eq_one_iff.mp h))
    have h2 : e.toMonoidHom g ∈ Subgroup.centralizer ({e.toMonoidHom t} : Set _) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]
    rw [h1] at h2
    obtain ⟨g', hg', hgg'⟩ := h2
    have hgg : g' = g := e.injective (by simpa using hgg')
    rwa [← hgg]
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
  obtain ⟨⟨t, ht⟩, ht1⟩ := exists_ne (1 : E)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hN : normalizer (E : Set X) ≤ fixedPoints α := by
    intro n hn
    rw [mem_fixedPoints]
    have hu : n⁻¹ * t * n ∈ E := by
      have := (mem_normalizer_iff.mp (inv_mem hn) t).mp ht
      simpa using this
    have hu1 : n⁻¹ * t * n ≠ 1 := fun h => ht1' (by
      have := congrArg (fun x => n * x * n⁻¹) h
      simpa [mul_assoc] using this)
    have hαu : α (n⁻¹ * t * n) = n⁻¹ * t * n := mem_fixedPoints.mp (hEα hu)
    have hαt : α t = t := mem_fixedPoints.mp (hEα ht)
    have hd : n⁻¹ * α n ∈ E := by
      refine hcent _ hu hu1 _ ?_
      have h1 : α n * (n⁻¹ * t * n) = t * α n := by
        have h3 : α (n * (n⁻¹ * t * n)) = α (t * n) := by congr 1; group
        rw [map_mul α n (n⁻¹ * t * n), map_mul α t n, hαu, hαt] at h3
        exact h3
      calc n⁻¹ * α n * (n⁻¹ * t * n) = n⁻¹ * (α n * (n⁻¹ * t * n)) := by group
        _ = n⁻¹ * (t * α n) := by rw [h1]
        _ = n⁻¹ * t * n * (n⁻¹ * α n) := by group
    have hαd : α (n⁻¹ * α n) = n⁻¹ * α n := mem_fixedPoints.mp (hEα hd)
    have hdd : (n⁻¹ * α n) * (n⁻¹ * α n) = 1 := by
      have h2 : α (α n) = n := apply_apply_of_orderOf hα n
      rw [map_mul, map_inv, h2] at hαd
      calc (n⁻¹ * α n) * (n⁻¹ * α n) = (α n)⁻¹ * n * (n⁻¹ * α n) := by rw [← hαd]
        _ = 1 := by group
    have hodd : orderOf (n⁻¹ * α n) ∣ 9 := by
      rw [← hE9, ← Subgroup.orderOf_mk (n⁻¹ * α n) hd]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (n⁻¹ * α n) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hdd])
    have h1 : orderOf (n⁻¹ * α n) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 (by norm_num)) hodd
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
    exact h1.symm
  have heq := RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_mulEquiv (e1.trans e2) hE9 hN
    (fixedPoints_ne_top hα)
  rw [heq, RankThree.PartTwo.KFacts.L34Max.card_normalizer_of_mulEquiv (e1.trans e2) hE9] at h360
  norm_num at h360

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h2 := two_mul_card_alternatingGroup (α := Fin 7)
  rw [Fintype.card_perm, Fintype.card_fin] at h2
  rw [Nat.card_eq_fintype_card]
  have h7 : Nat.factorial 7 = 5040 := by decide
  omega

theorem not_harrisF_A7 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 7)) : ¬ HarrisF 3 X := by
  intro hF
  have hcard : Nat.card X = 2520 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven]
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases harrisF_cases hF with ⟨n, hn, hm⟩ | ⟨α, hα, -, P, hPα, hP, hc⟩
  · rcases card_of_base hn hm with h | h <;> rw [hcard] at h <;> norm_num at h
  have hP9 : Nat.card P = 9 := card_eq_nine_of_noncyclic (by rw [hcard]; norm_num) hP hc
  obtain ⟨g, hg, h, hh, hg1, hg3, hh3, hgh, hhg⟩ := exists_pair_of_card_nine hP9 hc
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  set κ : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e α with hκdef
  obtain ⟨π, hπ⟩ := hbij.2 κ
  have hαα : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hππ : π * π = 1 := hbij.1 (by rw [map_mul, hπ, hκdef, ← map_mul, hαα, map_one, map_one])
  have hπ1 : π ≠ 1 := by
    rintro rfl
    rw [map_one, hκdef] at hπ
    have h1 : α = 1 := (MulAut.congr e).injective (by rw [← hπ, map_one])
    rw [h1, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hcomm : ∀ x ∈ P, ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * π =
      π * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    intro x hx
    have h1 : κ (e x) = e x := by
      change e (α (e.symm (e x))) = e x
      rw [MulEquiv.symm_apply_apply, mem_fixedPoints.mp (hPα hx)]
    rw [← hπ] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    calc ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * π
        = π * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * π⁻¹ * π := by rw [h2]
      _ = π * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by group
  have hcoe : ∀ y : X, ((e y : alternatingGroup (Fin 7)) : Perm (Fin 7)) ^ 3 = 1 ↔ y ^ 3 = 1 := by
    intro y
    rw [← Subgroup.coe_pow, ← map_pow, OneMemClass.coe_eq_one, e.map_eq_one_iff]
  have hres := a7_e9_check π hππ hπ1 _ _ ((hcoe g).mpr hg3) ((hcoe h).mpr hh3) (hcomm g hg)
    (hcomm h hh) (fun h1 => hg1 (e.map_eq_one_iff.mp (Subtype.ext h1)))
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hgh])
  apply hhg
  rcases hres with h1 | h1 | h1
  · have : h = 1 := e.map_eq_one_iff.mp (Subtype.ext h1)
    rw [this]
    exact one_mem _
  · have : h = g := e.injective (Subtype.ext h1)
    rw [this]
    exact mem_zpowers g
  · have : h = g * g := e.injective (Subtype.ext (by rw [h1, map_mul, Subgroup.coe_mul]))
    rw [this]
    exact mul_mem (mem_zpowers g) (mem_zpowers g)

theorem isSimpleGroup_of_harrisF {Y : Type} [Group Y] (h : HarrisF 3 Y) : IsSimpleGroup Y := by
  cases h with
  | base hY =>
    obtain ⟨n, -, hm⟩ := hY
    exact isSimpleGroup_of_lieModel_psl2 hm
  | blowup _ _ hb => exact hb.2.1

theorem l33For_of_twoNilpFor
    {C : (Y : Type) → [Group Y] → Prop} (h : TwoNilpFor C) : L33For C := by
  intro Y _ _ hC hY a ha hP
  rcases h Y hC (isSimpleGroup_of_harrisF hY) (C311.nonabelian_of_harrisF hY) a ha hP with
    ⟨p, f, hm⟩ | ⟨p, f, hm⟩ | hm | hm | hm
  · by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨-, -, h4, -⟩ := exists_psl2_of_lieModel hm
      refine ⟨f, ?_, hm⟩
      by_contra hf
      interval_cases f <;> norm_num at h4
    · exact absurd hY (not_harrisF_of_cyclic (cyclic_of_lieModel_psl2 hp3 hm))
  · exact absurd hY (not_harrisF_of_cyclic (cyclic_of_suzukiModel hm))
  · exact absurd hY (not_harrisF_L34 hm)
  · exact absurd hY (not_harrisF_of_cyclic (cyclic_of_lieModel_psu34 hm))
  · obtain ⟨e⟩ := hm
    exact absurd hY (not_harrisF_A7 e)

end CFSG.ComponentClassification.HarrisLit.L33
