module

public import CFSG.ClassicalInvolution.AschTight.S1911P3f
public import CFSG.ClassicalInvolution.AschTight.S1911P3a

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [IsSimpleGroup G] in
theorem mem_normalizer_perfectCoreIn (hd : Sec19Data p f K z S W) {a : G}
    {t : ↥(Subgroup.centralizer ({a} : Set G))} (htz : (t : G) * z = z * (t : G)) :
    t ∈ Subgroup.normalizer ((perfectCoreIn K a : Subgroup _) : Set ↥(Subgroup.centralizer
      ({a} : Set G))) := by
  have hN : (t : G) ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch,
      Subgroup.mem_centralizer_singleton_iff]
    exact htz
  have h := mem_normalizer_conjSub_of (K := K) 1 t (by rwa [OneMemClass.coe_one, conjSub_one])
  rwa [conjSub_one] at h

omit [Finite G] [IsSimpleGroup G] in
theorem two_lt_card_of_noncomm {H : Subgroup G} [Finite H] (h : ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) :
    2 < Nat.card H := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  by_contra hle
  have hpos : 0 < Nat.card H := Nat.card_pos
  rcases (by omega : Nat.card H = 1 ∨ Nat.card H = 2) with h1 | h2
  · rw [Subgroup.card_eq_one] at h1
    subst h1
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (by rw [hx, hy])
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : IsCyclic H := isCyclic_of_prime_card h2
    exact hxy (commute_of_isCyclic hc hx hy)

theorem false_of_fixes_nonabelian (hd : Sec19Data p f K z S W) {a : G}
    {t : ↥(Subgroup.centralizer ({a} : Set G))}
    (ht : ∃ g : G, (t : G) = g * z * g⁻¹) (htz : (t : G) * z = z * (t : G)) (ht2 : t * t = 1)
    (htne : (t : G) ≠ z)
    {P : Subgroup (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))} (hP2 : IsPGroup 2 P)
    (hPL : P ≤ secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a))
    (hfix : ∀ x ∈ P, @secAct _ _ (conjGen (perfectCoreIn K a))
      (conjGen_normal (perfectCoreIn K a)) t x = x)
    (hnc : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) : False := by
  have := conjGen_normal (perfectCoreIn K a)
  have hLY : perfectCoreIn K a ≤ conjGen (perfectCoreIn K a) := le_conjGen ⟨1, conjSub_one _⟩
  obtain ⟨Q, hQL, hQc, hQ2, ⟨e⟩⟩ := exists_lift_of_fixed (conjGen (perfectCoreIn K a)) ht2 hLY
    (mem_normalizer_perfectCoreIn hd htz) hP2 (hPL.trans le_rfl) hfix
  obtain ⟨g, hg⟩ := ht
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hIg := hI.conj g
  rw [← hg] at hIg
  have hJne : conjSub g K ≠ K := by
    intro h
    apply htne
    have hmem := hIg.mem
    rw [h] at hmem
    exact (hI.unique _ hmem hIg.sq).resolve_left hIg.ne_one
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hR2 : IsPGroup 2 (Q.map (Subgroup.centralizer ({a} : Set G)).subtype) := hQ2.map _
  refine false_of_le_inf_centralizer hd ⟨g, rfl⟩ (CoreAssembly.mem_conjClass_self K) hJne hIg hI
    hR2 ⟨((e.symm ⟨x, hx⟩ : ↥Q) : G), ⟨_, (e.symm ⟨x, hx⟩).2, rfl⟩,
      ((e.symm ⟨y, hy⟩ : ↥Q) : G), ⟨_, (e.symm ⟨y, hy⟩).2, rfl⟩, fun h => hxy ?_⟩ ?_ ?_ ?_
  · have h' : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ = e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ :=
      Subtype.ext (Subtype.ext h)
    have h'' := congrArg e h'
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h''
    exact congrArg Subtype.val h''
  · exact two_lt_card_of_noncomm ⟨_, ⟨_, (e.symm ⟨x, hx⟩).2, rfl⟩, _,
      ⟨_, (e.symm ⟨y, hy⟩).2, rfl⟩, fun h => hxy (by
        have h' : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ = e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ :=
          Subtype.ext (Subtype.ext h)
        have h'' := congrArg e h'
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h''
        exact congrArg Subtype.val h'')⟩
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact ((perfectResidualOf_le _).trans inf_le_left) (Subgroup.mem_subgroupOf.mp (hQL hq))
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hQc q hq).symm

theorem eq_of_secAct_fixes (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {t : ↥(Subgroup.centralizer ({a} : Set G))} (ht : ∃ g : G, (t : G) = g * z * g⁻¹)
    (htz : (t : G) * z = z * (t : G)) (ht2 : t * t = 1)
    (hfix : ∀ x ∈ secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a),
      @secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal (perfectCoreIn K a)) t x = x) :
    (t : G) = z := by
  by_contra htne
  have := conjGen_normal (perfectCoreIn K a)
  have hLY : perfectCoreIn K a ≤ conjGen (perfectCoreIn K a) := le_conjGen ⟨1, conjSub_one _⟩
  obtain ⟨R, hRL, hR2, x, hx, y, hy, hxy⟩ : ∃ R : Subgroup ↥(Subgroup.centralizer ({a} : Set G)),
      R ≤ perfectCoreIn K a ∧ IsPGroup 2 R ∧ ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(perfectCoreIn K a)) := inferInstance
    have hR : (T : Subgroup _).map (perfectCoreIn K a).subtype ∈
        RSet (CoreAssembly.conjClass (perfectCoreIn K a)) :=
      ⟨_, CoreAssembly.mem_conjClass_self _, T, rfl⟩
    exact ⟨_, Subgroup.map_subtype_le _, isPGroup_of_mem_rSet hR,
      (exists_ne_comm_of_mem_rSet hd.tight.branch.odd h5 hmem hR).1⟩
  have hP2 : IsPGroup 2 (secImg (conjGen (perfectCoreIn K a)) R) := hR2.comap_subtype.map _
  have hPL : secImg (conjGen (perfectCoreIn K a)) R ≤
      secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a) :=
    Subgroup.map_mono (Subgroup.comap_mono hRL)
  have hxY := hLY (hRL hx)
  have hyY := hLY (hRL hy)
  refine false_of_fixes_nonabelian hd ht htz ht2 htne hP2 hPL (fun w hw => hfix w (hPL hw))
    ⟨QuotientGroup.mk' _ ⟨x, hxY⟩, ⟨⟨x, hxY⟩, hx, rfl⟩,
      QuotientGroup.mk' _ ⟨y, hyY⟩, ⟨⟨y, hyY⟩, hy, rfl⟩, fun h => hxy ?_⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ↥(conjGen (perfectCoreIn K a)), x' = ⟨x, hxY⟩ := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ↥(conjGen (perfectCoreIn K a)), y' = ⟨y, hyY⟩ := ⟨_, rfl⟩
  rw [← hx', ← hy'] at h
  have hc : x' * y' * x'⁻¹ * y'⁻¹ ∈ classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have h' : (QuotientGroup.mk x' : _ ⧸ classicalInvolutionOddCore _) * QuotientGroup.mk y' =
        QuotientGroup.mk y' * QuotientGroup.mk x' := h
    rw [h']
    group
  have hc' : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (conjGen (perfectCoreIn K a)) := by
    refine ⟨x' * y' * x'⁻¹ * y'⁻¹, hc, ?_⟩
    rw [hx', hy']
    rfl
  have hcR : x * y * x⁻¹ * y⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc'
    (hR2.to_le (Subgroup.zpowers_le.mpr hcR))
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
