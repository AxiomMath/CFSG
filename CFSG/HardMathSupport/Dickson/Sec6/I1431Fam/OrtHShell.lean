module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

section Quotient

variable {Q : Type*} [Group Q] [Finite Q]

theorem t6orth_component_eq_of_le_sup_subnormal {ι : Type*} (M : ι → Subgroup Q)
    (hMn : ∀ i, (M i).IsSubnormal) (hMq : ∀ i, M i = ⊥ ∨ Open.IsQuasisimple (M i))
    {K : Subgroup Q} (hK : Open.IsComponentOf K ⊤) (hKM : K ≤ ⨆ i, M i) : ∃ i, K = M i := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ i, M i ≤ Subgroup.centralizer (K : Set Q) := by
    intro i
    rcases CFSG.LocalCores.component_subnormal_subgroup ((CFSG.isComponent_iff_open K).2 hK)
      (hMn i) with h | h
    · exfalso
      rcases hMq i with hbot | hq
      · exact ne_bot_of_isComponentOf hK (le_bot_iff.1 (hbot ▸ h))
      · have h1 : CFSG.Assembly.IsComponentOf K ⊤ := CFSG.Assembly.isComponentOf_iff_open.2 hK
        have h2 := CFSG.Assembly.IsComponentOf.of_le_of_le h1 h le_top
        have h3 : Open.IsComponentOf K (M i) := CFSG.Assembly.isComponentOf_iff_open.1 h2
        exact hne i
          (CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple h3 hq)
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact h))
  have hKc : K ≤ Subgroup.centralizer (K : Set Q) := hKM.trans (iSup_le hcomm)
  exact not_le_centralizer_of_isQuasisimple hK.2.2 hKc

end Quotient

section Blocks

variable {G : Type} [Group G] [Finite G]

theorem t6orth_exists_barX_eq_of_blocks {X J : Subgroup G} (hJ : GLAPComponent 3 X J) {ι : Type*}
    (N : ι → Subgroup G) (hNX : ∀ i, N i ≤ X)
    (hNsn : ∀ i, ((N i).subgroupOf X).IsSubnormal)
    (hNq : ∀ i, CFSG.IsQuasisimple (N i))
    (hk : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : G) ∈ ⨆ i, N i) :
    ∃ i, barX 3 X J = barX 3 X (N i) := by
  classical
  set O : Subgroup ↥X := GLAPPrimeCore 3 ↥X with hO
  set π : ↥X →* ↥X ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hLcomp : Open.IsComponentOf (barX 3 X J) ⊤ := hJ.2.2.1
  have hMn : ∀ i, (barX 3 X (N i)).IsSubnormal := fun i => (hNsn i).map hπs
  have hMq : ∀ i, barX 3 X (N i) = ⊥ ∨ Open.IsQuasisimple (barX 3 X (N i)) := by
    intro i
    by_cases hle : (N i).subgroupOf X ≤ π.ker
    · left
      exact (Subgroup.map_eq_bot_iff _).2 hle
    · right
      have hq : CFSG.IsQuasisimple ((N i).subgroupOf X) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hNX i)).symm
          (hNq i)
      obtain ⟨hp, hs, -⟩ := CFSG.LocalCores.isQuasisimple_map hq π hle
      exact ⟨hp.commutator_eq_top, hs⟩
  have hperf : ⁅barX 3 X J, barX 3 X J⁆ = barX 3 X J :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hLcomp.2.2.1)
  have hder : ∀ m : ℕ, barX 3 X J ≤ derivedSeries (↥X ⧸ O) m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
      rw [derivedSeries_succ]
      calc barX 3 X J = ⁅barX 3 X J, barX 3 X J⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono ih ih
  obtain ⟨k, hk⟩ := hk
  have hk' : derivedSeries ↥X k ≤ ⨆ i, (N i).subgroupOf X := by
    rw [← subgroupOf_iSup_eq N hNX]
    exact fun x hx => hk x hx
  have hLM : barX 3 X J ≤ ⨆ i, barX 3 X (N i) := by
    refine (hder k).trans ?_
    rw [← map_derivedSeries_eq hπs k]
    refine (Subgroup.map_mono hk').trans ?_
    rw [Subgroup.map_iSup]
    exact le_rfl
  exact t6orth_component_eq_of_le_sup_subnormal (fun i => barX 3 X (N i)) hMn hMq hLcomp hLM

theorem t6orth_exists_inner_of_blocks {X J : Subgroup G} (hJ : GLAPComponent 3 X J) {ι : Type*}
    (N : ι → Subgroup G) (hNX : ∀ i, N i ≤ X)
    (hNsn : ∀ i, ((N i).subgroupOf X).IsSubnormal)
    (hNq : ∀ i, CFSG.IsQuasisimple (N i))
    (hk : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : G) ∈ ⨆ i, N i)
    {b : G} (hbX : b ∈ X)
    (hb : ∀ i, barX 3 X (N i) = barX 3 X J →
      ∃ n ∈ N i, ∃ c ∈ X, (∀ m ∈ N i, c * m = m * c) ∧ b = n * c) :
    ∃ j₀ ∈ J, ∀ j ∈ J, ∀ (h1 : b * j * b⁻¹ ∈ X) (h2 : j₀ * j * j₀⁻¹ ∈ X),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b * j * b⁻¹, h1⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨j₀ * j * j₀⁻¹, h2⟩ := by
  classical
  obtain ⟨i, hi⟩ := t6orth_exists_barX_eq_of_blocks hJ N hNX hNsn hNq hk
  obtain ⟨n, hn, c, hcX, hcN, hbnc⟩ := hb i hi.symm
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  have hnbar : π ⟨n, hNX i hn⟩ ∈ barX 3 X J := by
    rw [hi]
    exact ⟨⟨n, hNX i hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
  obtain ⟨j₀', hj₀', hj₀π⟩ := hnbar
  refine ⟨(j₀' : G), Subgroup.mem_subgroupOf.1 hj₀', fun j hj h1 h2 => ?_⟩
  set c' : ↥X := ⟨c, hcX⟩ with hc'
  set n' : ↥X := ⟨n, hNX i hn⟩ with hn'
  set j' : ↥X := ⟨j, hJ.1 hj⟩ with hj'
  have hb' : (⟨b, hbX⟩ : ↥X) = n' * c' := Subtype.ext hbnc
  have hjbar : π j' ∈ barX 3 X (N i) := by
    rw [← hi]
    exact ⟨j', Subgroup.mem_subgroupOf.2 hj, rfl⟩
  obtain ⟨m', hm', hmπ⟩ := hjbar
  have hcm : c' * m' = m' * c' := Subtype.ext (hcN m' (Subgroup.mem_subgroupOf.1 hm'))
  have hcomm : π c' * π j' = π j' * π c' := by
    rw [← hmπ, ← map_mul, ← map_mul, hcm]
  have e1 : (⟨b * j * b⁻¹, h1⟩ : ↥X) = (⟨b, hbX⟩ : ↥X) * j' * (⟨b, hbX⟩ : ↥X)⁻¹ := rfl
  have e2 : (⟨(j₀' : G) * j * (j₀' : G)⁻¹, h2⟩ : ↥X) = j₀' * j' * j₀'⁻¹ := rfl
  have hj₀π' : π j₀' = π n' := hj₀π
  have h3 : π c' * π j' * (π c')⁻¹ = π j' := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [e1, e2, hb']
  simp only [map_mul, map_inv, hj₀π', mul_inv_rev]
  rw [show π n' * π c' * π j' * ((π c')⁻¹ * (π n')⁻¹) =
      π n' * (π c' * π j' * (π c')⁻¹) * (π n')⁻¹ by group, h3]

theorem t6orth_isTypeL2_of_barX_eq {X J N : Subgroup G} (hJ : GLAPComponent 3 X J) (hNX : N ≤ X)
    (hNq : CFSG.IsQuasisimple N) (hbar : barX 3 X J = barX 3 X N) {q : ℕ}
    (hq : IsTypeL2 q (barOf 3 J)) : IsTypeL2 q N := by
  have hJQ : Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_quotient_of_glaPComponent hJ
  have h1 : IsTypeL2 q ↥(barX 3 X J) :=
    p6_isTypeL2_of_equiv (barXEquiv Nat.prime_three hJ.2.1) hq
  have h2 : IsTypeL2 q ↥(barX 3 X N) := by
    rw [← hbar]
    exact h1
  have hnt : Nontrivial ↥(barX 3 X N) := by
    rw [← hbar]
    exact nontrivial_of_isQuasisimple' ((isQuasisimple_barX_iff Nat.prime_three hJ.2.1).2 hJQ)
  have hρs : Function.Surjective (barXHom 3 hNX) := barXHom_surjective 3 hNX
  have hcentral : (barXHom 3 hNX).ker ≤ Subgroup.center ↥N := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hNq (barXHom 3 hNX).normal_ker with h | h
    · exfalso
      have hsub : Subsingleton ↥(barX 3 X N) := ⟨fun u v => by
        obtain ⟨u', rfl⟩ := hρs u
        obtain ⟨v', rfl⟩ := hρs v
        have hu : u' ∈ (barXHom 3 hNX).ker := by rw [h]; exact Subgroup.mem_top u'
        have hv : v' ∈ (barXHom 3 hNX).ker := by rw [h]; exact Subgroup.mem_top v'
        rw [MonoidHom.mem_ker] at hu hv
        rw [hu, hv]⟩
      exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
    · exact h
  exact (isTypeL2_congr_of_central hNq.1 (barXHom 3 hNX) hρs hcentral).2 h2

end Blocks

section Shell

variable {Xs T : Type} [Group Xs] [Finite Xs] [Group T] [Finite T]

theorem t6orth_s1431_false_of_lift_blocks_sn (π : Xs →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Xs) (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {A : Subgroup (MulAut T)} {ψ : MulAut T} {J : Subgroup T} {q : ℕ} (c : S1431Cfg T A ψ J q)
    (hA : ∀ a ∈ A, IsInnerAut a)
    (data : ∀ a : Xs, a ^ 3 = 1 → π a ≠ 1 → ∃ (ι : Type) (_ : Finite ι) (N : ι → Subgroup Xs),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set Xs)) ∧
      (∀ i, ((N i).subgroupOf (Subgroup.centralizer ({a} : Set Xs))).IsSubnormal) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set Xs)) k,
        (g : Xs) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set Xs), b ^ 3 = 1 →
        ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹)) : False := by
  classical
  refine c.false_of_induced_inner ?_
  intro η hηA hηψ hstab
  obtain ⟨x, hx⟩ := hA ψ c.mem
  obtain ⟨y, hy⟩ := hA η hηA
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hx, hψ3, map_one])
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hy, hη3, map_one])
  have hxy : x * y = y * x := by
    apply hinj
    rw [map_mul, map_mul, hx, hy]
    have := c.elemAbelian.1.is_comm.comm ⟨ψ, c.mem⟩ ⟨η, hηA⟩
    exact congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact c.ne_one (by rw [← hx, map_one])
  obtain ⟨a, hax, ha3⟩ := exists_lift_cube' π hπ hker hZ3 hx3
  obtain ⟨b, hby, hb3⟩ := exists_lift_cube' π hπ hker hZ3 hy3
  have hba : b * a = a * b :=
    commute_of_lift π hker hZ3 ha3 (by rw [hax, hby]; exact hxy) |>.symm
  have hπa1 : π a ≠ 1 := by rw [hax]; exact hx1
  set X := Subgroup.centralizer ({π a} : Set T) with hX
  have hψX : fixSub ψ = X := by
    rw [← hx, ← hax, fixSub_conj_eq_centralizer]
  have hJ : GLAPComponent 3 X J := hψX ▸ c.comp
  have hbX : y ∈ X := by
    rw [hX, Subgroup.mem_centralizer_singleton_iff, hax]
    exact hxy.symm
  obtain ⟨ι, hfin, N, hNc, hNsn, hNq, hk, key⟩ := data a ha3 hπa1
  set C := Subgroup.centralizer ({a} : Set Xs) with hC
  have hXC : X = C.map π := centralizer_map_eq π hker hZ3 hπ ha3
  let N' : ι → Subgroup T := fun i => (N i).map π
  have hNX : ∀ i, N' i ≤ X := fun i => by
    rw [hXC]
    exact Subgroup.map_mono (hNc i)
  have hmemX : ∀ g : ↥C, π (g : Xs) ∈ X := by
    intro g
    rw [hXC]
    exact ⟨_, g.2, rfl⟩
  let π' : ↥C →* ↥X := (π.comp C.subtype).codRestrict X hmemX
  have hπ's : Function.Surjective π' := by
    intro z
    have hz : (z : T) ∈ C.map π := by
      rw [← hXC]
      exact z.2
    obtain ⟨g, hg, hgz⟩ := hz
    exact ⟨⟨g, hg⟩, Subtype.ext hgz⟩
  have hNsn' : ∀ i, ((N' i).subgroupOf X).IsSubnormal := by
    intro i
    have hmap : ((N i).subgroupOf C).map π' = (N' i).subgroupOf X := by
      ext z
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, Subgroup.mem_subgroupOf.mp hg, rfl⟩
      · intro hz
        obtain ⟨m, hm, hmz⟩ := Subgroup.mem_subgroupOf.mp hz
        exact ⟨⟨m, hNc i hm⟩, Subgroup.mem_subgroupOf.mpr hm, Subtype.ext hmz⟩
    rw [← hmap]
    exact (hNsn i).map hπ's
  have hNq' : ∀ i, CFSG.IsQuasisimple (N' i) := by
    intro i
    refine CFSG.LocalCores.isQuasisimple_map (hNq i) π fun hle => ?_
    have hle' : N i ≤ Subgroup.centralizer (N i : Set Xs) := fun g hg =>
      (Subgroup.mem_centralizer_iff).2 fun h hh => (Subgroup.mem_center_iff.mp (hker (hle hg)) h)
    exact not_le_centralizer_of_isQuasisimple (isQuasisimple_open (hNq i)) hle'
  have hk' : ∃ k : ℕ, ∀ g ∈ derivedSeries ↥X k, (g : T) ∈ ⨆ i, N' i := by
    obtain ⟨k, hk⟩ := hk
    refine ⟨k, fun g hg => ?_⟩
    rw [← map_derivedSeries_eq hπ's k] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have hmem := hk g0 hg0
    have h2 : π (g0 : Xs) ∈ (⨆ i, N i).map π := ⟨_, hmem, rfl⟩
    rw [Subgroup.map_iSup] at h2
    exact h2
  have hb : ∀ i, barX 3 X (N' i) = barX 3 X J →
      ∃ m ∈ N' i, ∃ g ∈ X, (∀ m' ∈ N' i, g * m' = m' * g) ∧ y = m * g := by
    intro i hi
    have hT' : IsTypeL2 q ↥(N' i) :=
      t6orth_isTypeL2_of_barX_eq hJ (hNX i) (hNq' i) hi.symm c.typeL2
    have hT : IsTypeL2 q ↥(N i) := by
      refine (isTypeL2_congr_of_central (hNq i).1 (π.subgroupMap (N i))
        (π.subgroupMap_surjective (N i)) ?_).2 hT'
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have hg1 : π (g : Xs) = 1 := congrArg Subtype.val hg
      have hgc : (g : Xs) ∈ Subgroup.center Xs := hker hg1
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hgc) g')
    have hbC : b ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact hba
    obtain ⟨s, hs, hsm⟩ := key i hT b hbC hb3
    refine ⟨π s, ⟨s, hs, rfl⟩, (π s)⁻¹ * y, ?_, ?_, ?_⟩
    · exact X.mul_mem (X.inv_mem (hNX i ⟨s, hs, rfl⟩)) hbX
    · rintro _ ⟨m0, hm0, rfl⟩
      have h2 : π b * π m0 * (π b)⁻¹ = π s * π m0 * (π s)⁻¹ := by
        have := congrArg π (hsm m0 hm0)
        simpa only [map_mul, map_inv] using this
      rw [hby] at h2
      calc (π s)⁻¹ * y * π m0 = (π s)⁻¹ * (y * π m0 * y⁻¹) * y := by group
        _ = (π s)⁻¹ * (π s * π m0 * (π s)⁻¹) * y := by rw [h2]
        _ = π m0 * ((π s)⁻¹ * y) := by group
    · rw [mul_inv_cancel_left]
  obtain ⟨j₀, hj₀, hbj⟩ := t6orth_exists_inner_of_blocks hJ N' hNX hNsn' hNq' hk' hbX hb
  subst hy
  exact isInnerAut_inducedBarHom_of_barX hJ hbX hstab hj₀ hbj

end Shell

end CFSG.HardMathSupport.Dickson.Sec6.I1431
