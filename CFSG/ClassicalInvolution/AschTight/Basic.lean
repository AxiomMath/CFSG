module

public import CFSG.ClassicalInvolution.AschTight.S19RCore

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem le_centralizer_of_tight (ht : S19R.TightStdDelta p f K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) :=
  isSubnormal_le ht.branch.member.subnormal

theorem uniqueInvolutionNormal_of_tight (ht : S19R.TightStdDelta p f K z) :
    UniqueInvolutionNormal K z := by
  have hz := ht.branch.member
  let Q : Sylow 2 K := Classical.choice Sylow.nonempty
  exact uniqueInvolutionNormal_of_quaternion_sylow hz.orderOf_eq_two hz.mem
    (le_centralizer_of_tight ht)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_centralizer_of_tight ht)).mpr
      ht.normEq.ge) Q (quaternion_sylow_of_isClassicalMember ht.branch.odd ht.branch.five hz Q)

theorem singleMemberControl_of_tight (ht : TightBranch p f K z) : SingleMemberControl K :=
  singleMemberControl_of_controlC ht.control ht.edgeless

theorem normalizer_eq_centralizer_of_tight (ht : S19R.TightStdDelta p f K z) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hU := uniqueInvolutionNormal_of_tight ht
  apply le_antisymm
  · intro n hn
    have hmem : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hU.2.1
    have hord : orderOf (n * z * n⁻¹) = 2 := by
      have := (MulAut.conj n).orderOf_eq z
      simpa [MulAut.conj_apply, hU.1] using this
    have h := hU.2.2.1 _ hmem hord
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]
  · exact ht.normEq.ge

theorem mem_of_isSylow2Of_of_tight (ht : S19R.TightStdDelta p f K z) {P : Subgroup G}
    (hP : IsSylow2Of P K) : z ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := uniqueInvolutionNormal_of_tight ht
  have h2K : 2 ∣ Nat.card K := by
    have h := Subgroup.orderOf_dvd_natCard K hU.2.1
    rwa [hU.1] at h
  have hPcard := hP.card_eq
  have h2P : 2 ∣ Nat.card P := by
    rw [hPcard]
    have hpos : 0 < (Nat.card K).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2K
    exact dvd_pow_self 2 hpos.ne'
  obtain ⟨⟨x, hxP⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have hx2' : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxP]; exact hx2
  rw [← hU.2.2.1 x (hP.1 hxP) hx2']
  exact hxP

theorem centralizer_le_of_mem_centralizer_of_tight (ht : TightBranch p f K z) {u : G}
    (hu : u ∈ Subgroup.centralizer (K : Set G)) (hu1 : u ≠ 1)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro c hc
  rw [← normalizer_eq_centralizer_of_tight (S19R.tightStdDelta_of_tightBranch ht),
    ← conjSubgroup_eq_self_iff]
  have hKu : K ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hu x hx
  have hKcu : conjSubgroup c K ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    have hx' : c⁻¹ * x * c ∈ K := mem_conjSubgroup_iff.mp hx
    have hcu : Commute c u := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm.symm
    have h1 : Commute (c⁻¹ * x * c) u :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hKu hx')).symm.symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx'' : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [hx'']
    exact ((hcu.mul_left h1).mul_left hcu.inv_left).eq
  exact singleMemberControl_of_tight ht u hu1 hu2 _
    (conjSubgroup_mem_conjugateSet c (self_mem_conjugateSet K)) K (self_mem_conjugateSet K)
    hKcu hKu

theorem conj_ne_of_mem_centralizer_of_tight (ht : TightBranch p f K z) {u : G}
    (hu : u ∈ Subgroup.centralizer (K : Set G)) (huz : u ≠ z) (g : G) : g * z * g⁻¹ ≠ u := by
  intro hgu
  have hs := S19R.tightStdDelta_of_tightBranch ht
  have hU := uniqueInvolutionNormal_of_tight hs
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h := hU.1
    simp at h
  have hu1 : u ≠ 1 := by
    intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * u * g := by rw [hgu]
      _ = 1 := by rw [h]; group
  have hu2 : orderOf u = 2 := by
    rw [← hgu]
    have := (MulAut.conj g).orderOf_eq z
    simpa [MulAut.conj_apply, hU.1] using this
  have hKu : K ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hu x hx
  have hKgu : conjSubgroup g K ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ K := mem_conjSubgroup_iff.mp hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hU.2.2.2.1 hx')
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgu]
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * x := by group
  have hgK : conjSubgroup g K = K :=
    singleMemberControl_of_tight ht u hu1 (isPGroup_two_zpowers_of_orderOf_two hu2) _
      (conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet K)) K (self_mem_conjugateSet K)
      hKgu hKu
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← normalizer_eq_centralizer_of_tight hs, ← conjSubgroup_eq_self_iff]
    exact hgK
  apply huz
  rw [← hgu, (Subgroup.mem_centralizer_singleton_iff.mp hgz).symm.symm]
  group

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g⁻¹ * x * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * x := by group

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_self :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer_of_mem_normalizer hg, fun h => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this

theorem centralizer_tightlyEmbedded_of_tight (ht : TightBranch p f K z) :
    classicalInvolutionTightlyEmbedded (Subgroup.centralizer (K : Set G)) := by
  intro g hg
  by_contra hodd
  have h2 : 2 ∣ Nat.card (↥(Subgroup.centralizer (K : Set G) ⊓
      (Subgroup.centralizer (K : Set G)).map (MulAut.conj g).toMonoidHom)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have := Fact.mk Nat.prime_two
  obtain ⟨⟨b, hb⟩, hb2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hb2' : orderOf b = 2 := by rw [← Subgroup.orderOf_mk b hb]; exact hb2
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb2'
  obtain ⟨hbC, hbCg⟩ := hb
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hbC x hx
  have hKgb : conjSubgroup g K ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ K := mem_conjSubgroup_iff.mp hx
    have hbg : g⁻¹ * b * g ∈ Subgroup.centralizer (K : Set G) := mem_conjSubgroup_iff.mp hbCg
    have h1 := Subgroup.mem_centralizer_iff.mp hbg _ hx'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * b = g * ((g⁻¹ * x * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = b * x := by group
  have hgK : conjSubgroup g K = K :=
    singleMemberControl_of_tight ht b hb1 (isPGroup_two_zpowers_of_orderOf_two hb2') _
      (conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet K)) K (self_mem_conjugateSet K)
      hKgb hKb
  exact hg (normalizer_le_normalizer_centralizer_self (conjSubgroup_eq_self_iff.mp hgK))

theorem normalizer_centralizer_eq_of_tight (ht : TightBranch p f K z) :
    Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
  have hs := S19R.tightStdDelta_of_tightBranch ht
  have hU := uniqueInvolutionNormal_of_tight hs
  rw [← normalizer_eq_centralizer_of_tight hs]
  refine le_antisymm (fun n hn => ?_) normalizer_le_normalizer_centralizer_self
  have hzC : z ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hU.2.2.2.1 hx)
  have hnz : n * z * n⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hn z).mp hzC
  have hz2 : orderOf (n * z * n⁻¹) = 2 := by
    have := (MulAut.conj n).orderOf_eq z
    simpa [MulAut.conj_apply, hU.1] using this
  have hz1 : n * z * n⁻¹ ≠ 1 := by
    intro h
    rw [h] at hz2
    simp at hz2
  have hKnz : K ≤ Subgroup.centralizer ({n * z * n⁻¹} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hnz x hx
  have hKnnz : conjSubgroup n K ≤ Subgroup.centralizer ({n * z * n⁻¹} : Set G) := by
    intro x hx
    have hx' : n⁻¹ * x * n ∈ K := mem_conjSubgroup_iff.mp hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hU.2.2.2.1 hx')
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * x := by group
  rw [← conjSubgroup_eq_self_iff]
  exact singleMemberControl_of_tight ht _ hz1 (isPGroup_two_zpowers_of_orderOf_two hz2) _
    (conjSubgroup_mem_conjugateSet n (self_mem_conjugateSet K)) K (self_mem_conjugateSet K)
    hKnnz hKnz

end CFSG.ClassicalInvolution.Disconnected.AschTight
