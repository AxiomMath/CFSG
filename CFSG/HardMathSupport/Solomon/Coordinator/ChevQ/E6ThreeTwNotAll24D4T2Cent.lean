module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint

section Generator

set_option linter.unusedSectionVars false

variable
  {L : Type} [Field L]

theorem d4t2_centralizer_generator (a : Fin Tag.E6.rank → Lˣ) (hap : ∀ i, a i ^ 3 = 1) :
    ∃ n ∈ toralCentralizer .E6 L a,
      n ∈ Subgroup.normalizer (toralRootGroup .E6 L a : Set (ModGL .E6 L)) ∧
      n ^ 3 ∈ toralRootGroup .E6 L a ∧
      ∀ g ∈ toralCentralizer .E6 L a, ∃ m ∈ toralRootGroup .E6 L a, ∃ j < 3,
        g = m * n ^ j := by
  obtain ⟨-, -, -, -, φ, hφ, hφw⟩ := Chevalley_toral_centralizer_root_generated_quotient .E6 L a
  by_cases hall : ∀ w : rootCharStabilizerSubgroup a, e6ShiftChar a w = 1
  · refine ⟨1, one_mem _, one_mem _, one_mem _, fun g hg => ?_⟩
    obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hwS : w ∈ kernelReflectionGroup a :=
      mem_kernelReflectionGroup_of_e6Shift a hap hw (hall ⟨w, hw⟩)
    have h1 : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup a ⧸
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hwS)
    rw [h1, map_one] at hq
    have h2 : (⟨g, hg⟩ : toralCentralizer .E6 L a) ∈
        (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a) :=
      (QuotientGroup.eq_one_iff _).1 hq.symm
    exact ⟨g, Subgroup.mem_subgroupOf.1 h2, 0, by norm_num, by simp⟩
  · push Not at hall
    obtain ⟨w₁, hw₁⟩ := hall
    set ω : Lˣ := e6ShiftChar a w₁ with hω
    have hω3 : ω ^ 3 = 1 := e6ShiftChar_pow_three a w₁
    set n : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L (w₁ : WeylGroup .E6) with hn
    have hnX : n ∈ toralCentralizer .E6 L a := canonicalRep_mem_toralCentralizer w₁.2
    have hnN : n ∈ Subgroup.normalizer (toralRootGroup .E6 L a : Set (ModGL .E6 L)) :=
      canonicalRep_mem_normalizer_toralRootGroup w₁.2
    have hdecomp : ∀ w ∈ rootCharStabilizerSubgroup a, ∃ j < 3, ∃ u ∈ kernelReflectionGroup a,
        w = u * (w₁ : WeylGroup .E6) ^ j := by
      intro w hw
      obtain ⟨j, hj, hjs⟩ := e6Line_exists_pow_eq_of_pow_three_eq_one hω3 hw₁
        (e6ShiftChar_pow_three a ⟨w, hw⟩)
      have hcj : (w₁ : WeylGroup .E6) ^ j ∈ rootCharStabilizerSubgroup a := pow_mem w₁.2 j
      have hu : w * ((w₁ : WeylGroup .E6) ^ j)⁻¹ ∈ rootCharStabilizerSubgroup a :=
        mul_mem hw (inv_mem hcj)
      refine ⟨j, hj, w * ((w₁ : WeylGroup .E6) ^ j)⁻¹, ?_, by group⟩
      refine mem_kernelReflectionGroup_of_e6Shift a hap hu ?_
      have h2 : e6ShiftChar a ⟨w * ((w₁ : WeylGroup .E6) ^ j)⁻¹, hu⟩ = 1 := by
        have e : (⟨w * ((w₁ : WeylGroup .E6) ^ j)⁻¹, hu⟩ : rootCharStabilizerSubgroup a) =
            ⟨w, hw⟩ * (w₁ ^ j)⁻¹ := rfl
        rw [e, map_mul, map_inv, map_pow, hjs, mul_inv_cancel]
      exact h2
    refine ⟨n, hnX, hnN, ?_, fun g hg => ?_⟩
    · have hw3 : (w₁ : WeylGroup .E6) ^ 3 ∈ rootCharStabilizerSubgroup a := pow_mem w₁.2 3
      have hk : (w₁ : WeylGroup .E6) ^ 3 ∈ kernelReflectionGroup a := by
        refine mem_kernelReflectionGroup_of_e6Shift a hap hw3 ?_
        have h2 : e6ShiftChar a ⟨(w₁ : WeylGroup .E6) ^ 3, hw3⟩ = 1 := by
          have e : (⟨(w₁ : WeylGroup .E6) ^ 3, hw3⟩ : rootCharStabilizerSubgroup a) = w₁ ^ 3 :=
            rfl
          rw [e, map_pow, hω3]
        exact h2
      have h1 : (QuotientGroup.mk (w₁ ^ 3) : rootCharStabilizerSubgroup a ⧸
          (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk)
      have h2 := hφw w₁
      have h3 : (QuotientGroup.mk ⟨n, hnX⟩ : toralCentralizer .E6 L a ⧸
          (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a)) ^ 3 = 1 := by
        rw [← h2, ← map_pow, ← QuotientGroup.mk_pow, h1, map_one]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
      exact Subgroup.mem_subgroupOf.1 h3
    · obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
      obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨j, hj, u, hu, rfl⟩ := hdecomp w hw
      have huW : u ∈ rootCharStabilizerSubgroup a := kernelReflectionGroup_le a hu
      have hmk : (QuotientGroup.mk ⟨u * (w₁ : WeylGroup .E6) ^ j, hw⟩ :
          rootCharStabilizerSubgroup a ⧸
            (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
              (QuotientGroup.mk w₁) ^ j := by
        have e : (⟨u * (w₁ : WeylGroup .E6) ^ j, hw⟩ : rootCharStabilizerSubgroup a) =
            ⟨u, huW⟩ * w₁ ^ j := rfl
        rw [e, QuotientGroup.mk_mul,
          (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu), one_mul,
          QuotientGroup.mk_pow]
      have hφc : φ (QuotientGroup.mk w₁) = QuotientGroup.mk ⟨n, hnX⟩ := hφw w₁
      rw [hmk, map_pow, hφc, ← QuotientGroup.mk_pow] at hq
      have h2 : (n ^ j)⁻¹ * g ∈ toralRootGroup .E6 L a :=
        Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hq)
      refine ⟨g * (n ^ j)⁻¹, ?_, j, hj, by group⟩
      have e : g * (n ^ j)⁻¹ = n ^ j * ((n ^ j)⁻¹ * g) * (n ^ j)⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hnN j) _).1 h2

theorem d4t2_le_of_not_mem (a : Fin Tag.E6.rank → Lˣ) (hap : ∀ i, a i ^ 3 = 1)
    {X N : Subgroup (ModGL .E6 L)} (hX : X ≤ toralCentralizer .E6 L a) (hNX : N ≤ X)
    (hX₀ : X ⊓ toralRootGroup .E6 L a ≤ N) {y : ModGL .E6 L} (hyN : y ∈ N)
    (hyM : y ∉ toralRootGroup .E6 L a) : X ≤ N := by
  obtain ⟨n, hnX, hnN, hn3, hgen⟩ := d4t2_centralizer_generator a hap
  obtain ⟨hMC, hMnormal, -⟩ := Chevalley_toral_centralizer_root_generated_quotient .E6 L a
  haveI : ((toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a)).Normal := hMnormal
  set π : toralCentralizer .E6 L a →* toralCentralizer .E6 L a ⧸
      (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a) :=
    QuotientGroup.mk' _ with hπ
  set q : toralCentralizer .E6 L a ⧸
      (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a) := π ⟨n, hnX⟩ with hq
  have hq3 : q ^ 3 = 1 := by
    rw [hq, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hn3)
  have hgenπ : ∀ g : toralCentralizer .E6 L a, ∃ j < 3, π g = q ^ j := by
    intro g
    obtain ⟨m, hm, j, hj, hg⟩ := hgen g.1 g.2
    refine ⟨j, hj, ?_⟩
    have e : g = ⟨m, hMC hm⟩ * ⟨n, hnX⟩ ^ j := Subtype.ext hg
    have h1 : π ⟨m, hMC hm⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hm)
    rw [e, map_mul, map_pow, ← hq, h1, one_mul]
  have hyC : y ∈ toralCentralizer .E6 L a := hX (hNX hyN)
  obtain ⟨k, hk, hyk⟩ := hgenπ ⟨y, hyC⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hyM
    rw [pow_zero] at hyk
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hyk)
  intro x hx
  obtain ⟨j, hj, hxj⟩ := hgenπ ⟨x, hX hx⟩
  have hs : π ⟨y, hyC⟩ ^ (j * k) = π ⟨x, hX hx⟩ := by
    rw [hxj, hyk, ← pow_mul]
    interval_cases k
    · omega
    · simp
    · have h4 : q ^ (2 * (j * 2)) = (q ^ 3) ^ j * q ^ j := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
      rw [h4, hq3, one_pow, one_mul]
  have hmem : (y ^ (j * k))⁻¹ * x ∈ toralRootGroup .E6 L a := by
    rw [← map_pow] at hs
    exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hs)
  have hyX : y ∈ X := hNX hyN
  have hX' : (y ^ (j * k))⁻¹ * x ∈ X := mul_mem (inv_mem (pow_mem hyX _)) hx
  have hN' : (y ^ (j * k))⁻¹ * x ∈ N := hX₀ ⟨hX', hmem⟩
  have e : x = y ^ (j * k) * ((y ^ (j * k))⁻¹ * x) := by group
  rw [e]
  exact mul_mem (pow_mem hyN _) hN'

theorem d4t2_exists_plane (a : Fin Tag.E6.rank → Lˣ) (hap : ∀ i, a i ^ 3 = 1)
    (hdT : rootDiagUnit .E6 a ∈ torusGroup .E6 L)
    {Eh : Subgroup (ModGL .E6 L)} (hEh : Eh ≤ toralCentralizer .E6 L a)
    (hab : IsElemAbelian 3 Eh) (hcard : Nat.card Eh = 3 ^ 3)
    (hd : rootDiagUnit .E6 a ∈ Eh) (hd1 : rootDiagUnit .E6 a ≠ 1) :
    ∃ F : Subgroup (ModGL .E6 L), F ≤ Eh ∧ F.relIndex Eh = 3 ∧ rootDiagUnit .E6 a ∈ F ∧
      F ≤ toralRootGroup .E6 L a := by
  obtain ⟨n, hnX, hnN, hn3, hgen⟩ := d4t2_centralizer_generator a hap
  obtain ⟨hMC, hMnormal, -⟩ := Chevalley_toral_centralizer_root_generated_quotient .E6 L a
  haveI : ((toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a)).Normal := hMnormal
  set π : toralCentralizer .E6 L a →* toralCentralizer .E6 L a ⧸
      (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a) :=
    QuotientGroup.mk' _ with hπ
  set q : toralCentralizer .E6 L a ⧸
      (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a) := π ⟨n, hnX⟩ with hq
  have hq3 : q ^ 3 = 1 := by
    rw [hq, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hn3)
  have hgenπ : ∀ g : toralCentralizer .E6 L a, ∃ j < 3, π g = q ^ j := by
    intro g
    obtain ⟨m, hm, j, hj, hg⟩ := hgen g.1 g.2
    refine ⟨j, hj, ?_⟩
    have e : g = ⟨m, hMC hm⟩ * ⟨n, hnX⟩ ^ j := Subtype.ext hg
    have h1 : π ⟨m, hMC hm⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hm)
    rw [e, map_mul, map_pow, ← hq, h1, one_mul]
  set ψ : Eh →* toralCentralizer .E6 L a ⧸
      (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a) :=
    π.comp (Subgroup.inclusion hEh) with hψ
  haveI hfq : Finite (Subgroup.zpowers q) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      exact (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hq3⟩).orderOf_pos.ne')
  have hrange : Nat.card ψ.range ≤ 3 := by
    have hle : ψ.range ≤ Subgroup.zpowers q := by
      rintro _ ⟨e, rfl⟩
      obtain ⟨j, -, hj⟩ := hgenπ (Subgroup.inclusion hEh e)
      exact ⟨j, by simpa [hψ, hj] using hj.symm⟩
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hq3
  have hd3 : rootDiagUnit .E6 a ^ 3 = 1 := hab.2 _ hd
  haveI hfd : Finite (Subgroup.zpowers (rootDiagUnit .E6 a)) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      exact (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hd3⟩).orderOf_pos.ne')
  have hex : ∃ e ∈ Eh, e ∈ toralRootGroup .E6 L a ∧
      e ∉ Subgroup.zpowers (rootDiagUnit .E6 a) := by
    by_contra hcon
    push Not at hcon
    have hker : Nat.card ψ.ker ≤ 3 := by
      have hker1 : ∀ x : ψ.ker, ((x : Eh) : ModGL .E6 L) ∈ toralRootGroup .E6 L a := by
        intro x
        have hx : ψ (x : Eh) = 1 := x.2
        have hx' : (QuotientGroup.mk (Subgroup.inclusion hEh (x : Eh)) : toralCentralizer .E6 L a ⧸
            (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a)) = 1 := hx
        exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N :=
          (toralRootGroup .E6 L a).subgroupOf (toralCentralizer .E6 L a))
            (Subgroup.inclusion hEh (x : Eh))).1 hx')
      let f : ψ.ker → Subgroup.zpowers (rootDiagUnit .E6 a) := fun x =>
        ⟨((x : Eh) : ModGL .E6 L), hcon _ (x : Eh).2 (hker1 x)⟩
      have hf : Function.Injective f := by
        intro x y hxy
        have h0 := Subtype.ext_iff.1 hxy
        exact Subtype.ext (Subtype.ext h0)
      refine (Nat.card_le_card_of_injective f hf).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hd3
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hcard] at h
    have : Nat.card ψ.ker * Nat.card ψ.range ≤ 3 * 3 := Nat.mul_le_mul hker hrange
    omega
  obtain ⟨e, heE, heM, hne⟩ := hex
  have hcomm : Commute (rootDiagUnit .E6 a) e :=
    congrArg Subtype.val (hab.1.is_comm.comm ⟨_, hd⟩ ⟨e, heE⟩)
  have he3 : e ^ 3 = 1 := hab.2 e heE
  have hFE : Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers e ≤ Eh :=
    sup_le (Subgroup.zpowers_le.2 hd) (Subgroup.zpowers_le.2 heE)
  refine ⟨Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers e, hFE,
    KSNotAll24.relIndex_eq_three hFE hcard
      (KSNotAll24.card_zpowers_sup_zpowers hcomm hd1 hd3 he3 hne),
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _),
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hdT)) (Subgroup.zpowers_le.2 heM)⟩

end Generator

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
