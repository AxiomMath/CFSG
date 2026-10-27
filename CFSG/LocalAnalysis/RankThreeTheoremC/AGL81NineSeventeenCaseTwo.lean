module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenExtremal
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111PsiLevel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111KappaMoves
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZNAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open Hyp111 CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem exists_perfect_cover [Fact p.Prime] {M H N : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1)
    (hKX : ¬ K ≤ d1X0 p M H) (hcov : AGLCovers p H N K)
    (hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M) :
    ∃ (W : Subgroup G) (_ : W ≤ H ⊓ N) (J : Subgroup (N ⧸ primeComplementCore (G := N) p))
      (φ : J →* K),
      (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K ∧
      (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) = J ∧
      Function.Surjective φ ∧ Group.IsPerfect J ∧ ((d1X0 p M N).subgroupOf J).map φ ≠ ⊤ := by
  classical
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) p)
  set W₀ : Subgroup G := (H ⊓ N) ⊓ (K.comap πH).map H.subtype with hW₀def
  have hW₀H : W₀ ≤ H := inf_le_left.trans inf_le_left
  have hW₀N : W₀ ≤ N := inf_le_left.trans inf_le_right
  have hW₀K : ∀ {g : G} (hg : g ∈ W₀), πH ⟨g, hW₀H hg⟩ ∈ K := by
    rintro g ⟨-, h, hh, hhg⟩
    have : h = ⟨g, hW₀H ⟨‹_›, h, hh, hhg⟩⟩ := Subtype.ext hhg
    exact this ▸ hh
  have hψ₀ : ∀ w : W₀, πH (Subgroup.inclusion hW₀H w) ∈ K := fun w => hW₀K w.2
  set ψ : W₀ →* K := (πH.comp (Subgroup.inclusion hW₀H)).codRestrict K hψ₀
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := hcov hk
    have hhN : (h : G) ∈ H ⊓ N := Subgroup.mem_subgroupOf.mp hh
    exact ⟨⟨h, hhN, h, hk, rfl⟩, rfl⟩
  set ρ : W₀ →* N ⧸ primeComplementCore (G := N) p := πN.comp (Subgroup.inclusion hW₀N)
  obtain ⟨x, hx1, kx, hxk⟩ := hKp
  haveI := hKs
  have hker : ρ.rangeRestrict.ker ≤ ψ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact le_ker_of_isSimpleGroup ψ hψs ρ.ker
      (fun n hn => coprime_of_mk_inclusion_eq_one3 hW₀N n hn) hx1 hxk
  obtain ⟨φ₀, hφ₀ρ, hφ₀s, -⟩ := exists_surjective_comp_eq ρ.rangeRestrict
    ρ.rangeRestrict_surjective ψ hψs hker
  obtain ⟨J, ⟨hJ, hJs⟩, hmin⟩ := Set.exists_min_image
    {J : Subgroup (N ⧸ primeComplementCore (G := N) p) |
      ∃ h : J ≤ ρ.range, Function.Surjective (φ₀.comp (Subgroup.inclusion h))}
    (fun J => Nat.card J) (Set.toFinite _)
    ⟨ρ.range, le_rfl, fun k => let ⟨j, hj⟩ := hφ₀s k; ⟨j, hj⟩⟩
  set φ := φ₀.comp (Subgroup.inclusion hJ)
  have hφlift : ∀ (j : J) (w : W₀), ρ w = j → φ j = ψ w := by
    intro j w hw
    have h2 : ρ.rangeRestrict w = Subgroup.inclusion hJ j := Subtype.ext hw
    rw [← hφ₀ρ w, h2]
    rfl
  have hKper : commutator K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hKnab
      have h1 : (⊤ : Subgroup K) ≤ Subgroup.centralizer ((⊤ : Subgroup K) : Set K) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact hbot)
      exact hab (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top b)) a trivial)
    · exact htop
  set C := (commutator J).map J.subtype
  have hCJ : C ≤ J := Subgroup.map_subtype_le _
  have hCs : Function.Surjective (φ₀.comp (Subgroup.inclusion (hCJ.trans hJ))) := by
    intro k
    have hk : k ∈ (commutator J).map φ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hJs,
        ← commutator_def, hKper]
      trivial
    obtain ⟨c, hc, rfl⟩ := hk
    exact ⟨⟨c, c, hc, rfl⟩, rfl⟩
  have hCeq : C = J := Subgroup.eq_of_le_of_card_ge hCJ (hmin C ⟨hCJ.trans hJ, hCs⟩)
  have hJper : Group.IsPerfect J := by
    refine ⟨Subgroup.map_injective J.subtype_injective ?_⟩
    show C = _
    rw [hCeq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set W : Subgroup G := W₀ ⊓ (J.comap πN).map N.subtype
  have hWW₀ : W ≤ W₀ := inf_le_left
  refine ⟨W, hWW₀.trans inf_le_left, J, φ, ?_, ?_, hJs, hJper, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      exact hW₀K (hWW₀ (Subgroup.mem_subgroupOf.mp hh))
    · intro k hk
      obtain ⟨j, hj⟩ := hJs ⟨k, hk⟩
      obtain ⟨w, hw⟩ := hJ j.2
      refine ⟨Subgroup.inclusion hW₀H w,
        Subgroup.mem_subgroupOf.mpr ⟨w.2, Subgroup.inclusion hW₀N w, ?_, rfl⟩, ?_⟩
      · show ρ w ∈ J
        rw [hw]; exact j.2
      · have h1 := hφlift j w hw
        rw [hj] at h1
        exact (congrArg Subtype.val h1).symm
  · apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      obtain ⟨-, n', hn', hn'n⟩ := Subgroup.mem_subgroupOf.mp hn
      have : n' = n := Subtype.ext hn'n
      exact this ▸ hn'
    · intro j hj
      obtain ⟨w, hw⟩ := hJ hj
      refine ⟨Subgroup.inclusion hW₀N w,
        Subgroup.mem_subgroupOf.mpr ⟨w.2, Subgroup.inclusion hW₀N w, ?_, rfl⟩, hw⟩
      show ρ w ∈ J
      rw [hw]; exact hj
  · intro htop
    apply hKX
    intro k hk
    obtain ⟨j, hj, hjk⟩ : (⟨k, hk⟩ : K) ∈ ((d1X0 p M N).subgroupOf J).map φ :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmj⟩ := Subgroup.mem_subgroupOf.mp hj
    obtain ⟨w, hw⟩ := hJ j.2
    have hwk : ψ w = ⟨k, hk⟩ := (hφlift j w hw).symm.trans hjk
    have hmw : πN m = πN (Subgroup.inclusion hW₀N w) := hmj.trans hw.symm
    have ho : m⁻¹ * Subgroup.inclusion hW₀N w ∈ primeComplementCore (G := N) p :=
      QuotientGroup.eq.mp hmw
    have hoM : ((m⁻¹ * Subgroup.inclusion hW₀N w : N) : G) ∈ M := hcore ⟨_, ho, rfl⟩
    have hwM : (w : G) ∈ M := by
      have e : (w : G) = (m : G) * ((m⁻¹ * Subgroup.inclusion hW₀N w : N) : G) := by
        simp [Subgroup.coe_inclusion]
      rw [e]
      exact M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 hoM
    exact ⟨Subgroup.inclusion hW₀H w, Subgroup.mem_subgroupOf.mpr ⟨hW₀H w.2, hwM⟩,
      congrArg Subtype.val hwk⟩

theorem false_of_layer_eq_bot_of_surjective [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {T : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X T X₀)
    (hlayer : CFSG.layer X = ⊥) {J : Subgroup X} {S : Type*} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (φ : J →* S)
    (hφ : Function.Surjective φ) (hS2 : p ^ 2 ∣ Nat.card S) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hET, -, hEc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h.three_le_pRank
  haveI : Nontrivial (T : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h1 : Nat.card E ≤ Nat.card (T : Subgroup X) := Subgroup.card_le_of_le hET
    have h2 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  haveI := IsPGroup.center_nontrivial T.isPGroup'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_subgroup (Subgroup.center T))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (by rw [hk]; exact dvd_pow_self p hk0)
  have hzc : ((z : T) : X) ∈ Subgroup.centralizer ((T : Subgroup X) : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩)
  have hzo : orderOf ((z : T) : X) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrel, -, -⟩ :=
    h.structure_of_layer_eq_bot3 hlayer hzc hzo
  set Q := CFSG.pCore p X
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  have hQT : Q ≤ (T : Subgroup X) := hQp.le_sylow_of_normal T
  set D := Q.subgroupOf J
  have hDker : D ≤ φ.ker := by
    have hDn : (D.map φ).Normal := (Subgroup.normal_subgroupOf).map φ hφ
    haveI := hS
    haveI := hDn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map φ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      have hSp : IsPGroup p S := by
        have hDp : IsPGroup p D := hQp.comap_subtype
        have := hDp.map φ
        rw [ht] at this
        exact this.of_equiv Subgroup.topEquiv
      haveI : Nontrivial S := inferInstance
      have hc := IsPGroup.center_nontrivial hSp
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
      · exact (Subgroup.nontrivial_iff_ne_bot _).mp hc hb
      · obtain ⟨a, b, hab⟩ := hSnab
        exact hab (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)
  have hJ1 : Nat.card S * Nat.card φ.ker = Nat.card J := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have hDdvd : Nat.card D ∣ Nat.card φ.ker := Subgroup.card_dvd_of_le hDker
  have hidx := Subgroup.index_mul_card D
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h2 : p ^ 2 ∣ Q.relIndex J := by
    obtain ⟨c, hc⟩ := hDdvd
    have : Nat.card S * c = D.index := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hidx, ← hJ1, hc]; ring
    exact (hS2.trans (Dvd.intro c this))
  rw [← Subgroup.relIndex_sup_right J Q] at h2
  have e1 := Subgroup.relIndex_mul_card (H := Q) (K := J ⊔ Q)
  rw [inf_of_le_left le_sup_right] at e1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  have h3 : p ^ (2 + n) ∣ Nat.card X := by
    rw [pow_add, ← hn]
    exact (Nat.mul_dvd_mul_right h2 _).trans (e1 ▸ Subgroup.card_subgroup_dvd_card _)
  have h4 := T.pow_dvd_card_of_pow_dvd_card h3
  have e2 := Subgroup.relIndex_mul_card (H := Q) (K := (T : Subgroup X))
  rw [inf_of_le_left hQT, hrel, hn, ← pow_succ'] at e2
  rw [← e2] at h4
  have := Nat.pow_dvd_pow_iff_le_right hp.one_lt |>.mp h4
  omega

theorem D1Extremal.false_of_hasPrimeConstraint_of_surjective {P' : Sylow p G} {M N T : Subgroup G}
    (hext : D1Extremal p P' M N T) (hc : HasPrimeConstraint (G := N) p)
    {J : Subgroup (N ⧸ primeComplementCore (G := N) p)} {S : Type*} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (φ : J →* S)
    (hφ : Function.Surjective φ) (hS2 : p ^ 2 ∣ Nat.card S) : False := by
  have : Fact p.Prime := ⟨hext.prime⟩
  obtain ⟨Tbar, -, hred⟩ := hext.toD1Escape.reducedNongeneration
  exact false_of_layer_eq_bot_of_surjective hred (layer_eq_bot_of_exists_selfCentralizing hc) hS
    hSnab φ hφ hS2

theorem exists_surjective_cover [Fact p.Prime] {H N : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKs : IsSimpleGroup K)
    (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1) (hcov : AGLCovers p H N K) :
    ∃ (J : Subgroup (N ⧸ primeComplementCore (G := N) p)) (φ : J →* K), Function.Surjective φ := by
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) p)
  set W₀ : Subgroup G := (H ⊓ N) ⊓ (K.comap πH).map H.subtype with hW₀def
  have hW₀H : W₀ ≤ H := inf_le_left.trans inf_le_left
  have hW₀N : W₀ ≤ N := inf_le_left.trans inf_le_right
  have hW₀K : ∀ {g : G} (hg : g ∈ W₀), πH ⟨g, hW₀H hg⟩ ∈ K := by
    rintro g ⟨-, h, hh, hhg⟩
    have : h = ⟨g, hW₀H ⟨‹_›, h, hh, hhg⟩⟩ := Subtype.ext hhg
    exact this ▸ hh
  have hψ₀ : ∀ w : W₀, πH (Subgroup.inclusion hW₀H w) ∈ K := fun w => hW₀K w.2
  set ψ : W₀ →* K := (πH.comp (Subgroup.inclusion hW₀H)).codRestrict K hψ₀
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := hcov hk
    have hhN : (h : G) ∈ H ⊓ N := Subgroup.mem_subgroupOf.mp hh
    exact ⟨⟨h, hhN, h, hk, rfl⟩, rfl⟩
  set ρ : W₀ →* N ⧸ primeComplementCore (G := N) p := πN.comp (Subgroup.inclusion hW₀N)
  obtain ⟨x, hx1, kx, hxk⟩ := hKp
  haveI := hKs
  have hker : ρ.rangeRestrict.ker ≤ ψ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact le_ker_of_isSimpleGroup ψ hψs ρ.ker
      (fun n hn => coprime_of_mk_inclusion_eq_one3 hW₀N n hn) hx1 hxk
  obtain ⟨φ₀, -, hφ₀s, -⟩ := exists_surjective_comp_eq ρ.rangeRestrict
    ρ.rangeRestrict_surjective ψ hψs hker
  exact ⟨ρ.range, φ₀, hφ₀s⟩

theorem D1Extremal.false_of_hasPrimeConstraint_of_cover {P' : Sylow p G} {M H N T : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hext : D1Extremal p P' M N T)
    (hc : HasPrimeConstraint (G := N) p) (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1)
    (hcov : AGLCovers p H N K) (hK2 : p ^ 2 ∣ Nat.card K) : False := by
  have : Fact p.Prime := ⟨hext.prime⟩
  obtain ⟨J, φ, hφs⟩ := exists_surjective_cover hKs hKp hcov
  exact D1Extremal.false_of_hasPrimeConstraint_of_surjective hext hc hKs hKnab φ hφs hK2

theorem sq_dvd_card_of_not_isCyclic [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (hY : IsPGroup p Y) (hnc : ¬ IsCyclic Y) : p ^ 2 ∣ Nat.card Y := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
  rw [hk]
  refine pow_dvd_pow p ?_
  by_contra hlt
  push Not at hlt
  interval_cases k
  · rw [pow_zero] at hk
    haveI := (Nat.card_eq_one_iff_unique.mp hk).1
    exact hnc isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact hnc (isCyclic_of_prime_card hk)

theorem factor_of_forall_mul {M H N W : Subgroup G} (hW : W ≤ H ⊓ N)
    (hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M)
    (h : ∀ y : N ⧸ primeComplementCore (G := N) p, ∃ a ∈ d1X0 p M N,
      ∃ j ∈ (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)), y = a * j) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y := by
  intro x hx
  obtain ⟨_, ⟨m, hm, rfl⟩, _, ⟨w, hw, rfl⟩, hxe⟩ :=
    h (QuotientGroup.mk' (primeComplementCore (G := N) p) ⟨x, hx⟩)
  have h1 : QuotientGroup.mk' (primeComplementCore (G := N) p) (m⁻¹ * (⟨x, hx⟩ * w⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hxe]; group
  have hoM : ((m⁻¹ * (⟨x, hx⟩ * w⁻¹) : N) : G) ∈ M :=
    hcore ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hxw : x * (w : G)⁻¹ ∈ M := by
    have e : x * (w : G)⁻¹ = (m : G) * ((m⁻¹ * (⟨x, hx⟩ * w⁻¹) : N) : G) := by simp
    rw [e]
    exact M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 hoM
  exact ⟨x * (w : G)⁻¹, ⟨N.mul_mem hx (N.inv_mem w.2), hxw⟩, w,
    hW (Subgroup.mem_subgroupOf.mp hw), by group⟩

theorem hyp917Ext_of_caseTwoGroup (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hOut : KFactOutCyclic) (hSz : KFactSeitzCyc)
    (hInv : KFactCaseTwoInvIn G) (hS : Setting G) (hpA : p ∈ rankThreeSigmaA G)
    (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q)
    {M H B : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1) (hiso : IsCaseTwoGroup p K)
    (hK2 : p ^ 2 ∣ Nat.card K) (hKX : ¬ K ≤ d1X0 p M H) (hκ : d1Kappa p M H ≤ Nat.card K) :
    Hyp917Ext p M H B K := by
  intro P' N T hP' _ hcov hNH
  have hp := hP'.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hc : HasPrimeConstraint (G := N) p
  · exact (D1Extremal.false_of_hasPrimeConstraint_of_cover hP' hc hKs hKnab hKp hcov hK2).elim
  obtain ⟨Tbar, hcfg⟩ := exists_componentConfig3 hS hpA ⟨hP'.maxTwoLocal_M, hP'.weakCore_le⟩ hP'
    hc hind
  have he := hcfg.ext.toD1Escape
  have hcore := D1Escape.core_map_le he
  obtain ⟨W, hW, J, φ, hWK, hWJ, hφs, hJper, hY₀⟩ :=
    exists_perfect_cover hKs hKnab hKp hKX hcov hcore
  have hκN : Nat.card (d1KBar p M N) ≤ Nat.card K := hNH.trans hκ
  have hKJ : Nat.card K ≤ Nat.card J := Nat.card_le_card_of_surjective φ hφs
  by_cases hall : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
      IsCyclic ((Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ L :
        Subgroup (N ⧸ primeComplementCore (G := N) p))
  ·
    have hdU : D1CaseTwoDataU p P' M N T Tbar := ⟨hcfg, hall⟩
    obtain ⟨L₁, h₁, hL₁, hL₁c⟩ := hdU.exists_caseTwo_not_le hOut hSz
    have hL₁K : Nat.card L₁ ≤ Nat.card K := (Subgroup.card_le_of_le (le_d1KBar h₁ hL₁)).trans hκN
    by_cases huniq : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
        L = L₁
    ·
      have hn : L₁.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hL : IsComponentOf (L₁.map (MulAut.conj g).toMonoidHom) ⊤ :=
          (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L₁).mpr h₁
        rw [← huniq _ hL]
        exact ⟨n, hn, rfl⟩
      have hJlay := hcfg.red.le_layer_of_isPerfect hcfg.catalog hSch h₁ hJper fun L hL => by
        rw [huniq L hL, Subgroup.normalizer_eq_top_iff.mpr hn]
        exact le_top
      have hlay : CFSG.layer (N ⧸ primeComplementCore (G := N) p) ≤ L₁ :=
        sSup_le fun L hL => (huniq L ((CFSG.isComponent_iff_open L).mp hL)).le
      have hJL : J = L₁ := Subgroup.eq_of_le_of_card_ge (hJlay.trans hlay) (hL₁K.trans hKJ)
      have hA := hcfg.red.cycAutRankLeTwo_of_kFactOutCyclic hcfg.catalog hOut
      have hO := hcfg.red.pCore_ne_bot_of_unique_of_aut hA hall hdU.rank h₁ huniq
      obtain ⟨z, hz, hzp⟩ : ∃ z ∈ CFSG.pCore p (N ⧸ primeComplementCore (G := N) p),
          orderOf z = p := by
        obtain ⟨z, hz⟩ : ∃ x : CFSG.pCore p (N ⧸ primeComplementCore (G := N) p),
            orderOf x = p := by
          rcases (CFSG.pCore_isPGroup (p := p)
              (G := N ⧸ primeComplementCore (G := N) p)).card_eq_or_dvd with h1 | hdvd
          · exact absurd (Subgroup.card_eq_one.mp h1) hO
          · exact exists_prime_orderOf_dvd_card' p hdvd
        exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
      obtain ⟨T₁, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Tbar
        (Subgroup.Normal.isSubnormal hn)
      have htop := Sylow.normalizer_sup_eq_top T₁
      rw [hT₁] at htop
      have htop' : (⊤ : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N ⊔ L₁ := by
        rw [← htop]
        exact sup_le_sup_right (hcfg.red.normalizer_inf_le_of_pCore h₁ (hall L₁ h₁) hz hzp) _
      refine factor_of_forall_mul hW hcore fun y => ?_
      obtain ⟨a, ha, l, hl, hal⟩ := Subgroup.mem_sup_of_normal_right.mp (htop' (Subgroup.mem_top y))
      exact ⟨a, ha, l, hWJ ▸ hJL ▸ hl, hal.symm⟩
    push Not at huniq
    obtain ⟨L₂, h₂, hne⟩ := huniq
    by_cases hL₂ : L₂ ≤ d1X0 p M N
    ·
      obtain ⟨hn₁, hn₂⟩ := hcfg.red.normal_of_two_components hall h₁ h₂ hL₁ hL₂
      have hJlay := hcfg.red.le_layer_of_isPerfect hcfg.catalog hSch h₁ hJper fun L hL => by
        rcases hcfg.red.eq_or_eq_of_isComponentOf h₁ h₂ hne.symm hL with h | h
        · rw [h, Subgroup.normalizer_eq_top_iff.mpr hn₁]; exact le_top
        · rw [h, Subgroup.normalizer_eq_top_iff.mpr hn₂]; exact le_top
      have hlay : CFSG.layer (N ⧸ primeComplementCore (G := N) p) ≤ L₁ ⊔ L₂ := by
        refine sSup_le fun L hL => ?_
        rcases hcfg.red.eq_or_eq_of_isComponentOf h₁ h₂ hne.symm
            ((CFSG.isComponent_iff_open L).mp hL) with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      have hker : L₂.subgroupOf J ≤ φ.ker := by
        have hnorm : ((L₂.subgroupOf J).map φ).Normal :=
          (Subgroup.normal_subgroupOf).map φ hφs
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L₂.subgroupOf J).map φ) with hbot | htop
        · exact (Subgroup.map_eq_bot_iff _).mp hbot
        · refine absurd (eq_top_iff.mpr (htop.symm.le.trans (Subgroup.map_mono fun j hj =>
            Subgroup.mem_subgroupOf.mpr (hL₂ (Subgroup.mem_subgroupOf.mp hj))))) hY₀
      have hrJ : Nat.card K ≤ L₂.relIndex J := by
        have e1 := Subgroup.index_mul_card (L₂.subgroupOf J)
        have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv] at e2
        have e3 := Subgroup.card_le_of_le hker
        have hpos : 0 < Nat.card (L₂.subgroupOf J) := Nat.card_pos
        show Nat.card K ≤ (L₂.subgroupOf J).index
        by_contra hlt
        push Not at hlt
        have : (L₂.subgroupOf J).index * Nat.card (L₂.subgroupOf J) <
            Nat.card K * Nat.card φ.ker :=
          calc (L₂.subgroupOf J).index * Nat.card (L₂.subgroupOf J)
              < Nat.card K * Nat.card (L₂.subgroupOf J) := Nat.mul_lt_mul_of_pos_right hlt hpos
            _ ≤ Nat.card K * Nat.card φ.ker := Nat.mul_le_mul_left _ e3
        omega
      have hr1 : L₂.relIndex L₁ ≤ Nat.card L₁ := by
        have e := Subgroup.relIndex_mul_card (H := L₂) (K := L₁)
        have hpos : 0 < Nat.card (L₂ ⊓ L₁ : Subgroup _) := Nat.card_pos
        nlinarith
      have hsJ : L₂.relIndex (J ⊔ L₂) = L₂.relIndex J := Subgroup.relIndex_sup_right J L₂
      have hs1 : L₂.relIndex (L₁ ⊔ L₂) = L₂.relIndex L₁ := Subgroup.relIndex_sup_right L₁ L₂
      have hle : J ⊔ L₂ ≤ L₁ ⊔ L₂ := sup_le (hJlay.trans hlay) le_sup_right
      have heq : J ⊔ L₂ = L₁ ⊔ L₂ := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        have c1 := Subgroup.relIndex_mul_card (H := L₂) (K := J ⊔ L₂)
        have c2 := Subgroup.relIndex_mul_card (H := L₂) (K := L₁ ⊔ L₂)
        rw [inf_of_le_left le_sup_right] at c1 c2
        rw [← c1, ← c2, hsJ, hs1]
        exact Nat.mul_le_mul_right _ ((hr1.trans hL₁K).trans hrJ)
      have htop := hcfg.red.top_le_sup_layer hall h₁ h₂ hne.symm
      have : (CFSG.layer (N ⧸ primeComplementCore (G := N) p)).Characteristic :=
        CFSG.LocalCores.layer_characteristic
      refine factor_of_forall_mul hW hcore fun y => ?_
      obtain ⟨a, ha, d, hd, had⟩ := Subgroup.mem_sup_of_normal_right.mp (htop (Subgroup.mem_top y))
      have hd' : d ∈ L₂ ⊔ J := by rw [sup_comm, heq]; exact hlay hd
      obtain ⟨c, hc, j, hj, hcj⟩ := Subgroup.mem_sup_of_normal_left.mp hd'
      refine ⟨a * c, (d1X0 p M N).mul_mem ha (hL₂ hc), j, hWJ ▸ hj, ?_⟩
      rw [← had, ← hcj, mul_assoc]
    ·
      exfalso
      obtain ⟨e⟩ := nonempty_mulEquiv_of_isCaseTwoGroup hL₁c hiso
      have hsup : L₁ ⊔ L₂ ≤ d1KBar p M N := sup_le (le_d1KBar h₁ hL₁) (le_d1KBar h₂ hL₂)
      have hcard : Nat.card (L₁ ⊔ L₂ : Subgroup _) ≤ Nat.card L₁ := by
        rw [Nat.card_congr e.toEquiv]
        exact (Subgroup.card_le_of_le hsup).trans hκN
      have hL₂L₁ : L₂ ≤ L₁ :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_left : L₁ ≤ L₁ ⊔ L₂) hcard).symm ▸ le_sup_right
      obtain ⟨a, b, hab⟩ := (hcfg.red.isSimpleGroup_of_isCyclic hcfg.catalog h₂ (hall L₂ h₂)).2.1
      rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open L₁).mpr h₁)
          ((CFSG.isComponent_iff_open L₂).mpr h₂) with heq | hcomm
      · exact hne heq.symm
      · have hmem := Subgroup.commutator_mem_commutator (hL₂L₁ a.2) b.2
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hab (Subtype.ext hmem)
  push Not at hall
  obtain ⟨K', hK', hnc'⟩ := hall
  rcases hcfg.red.rankOne_or_center hK' hnc' with ⟨z, hzR, hzK, hzp, hzc, -, -, -, -⟩ | hcent
  ·
    exact (hcfg.red.false_of_surjective_of_rankOne_at hcfg.catalog hInv.on hSch
      hcfg.pRank_rbar_eq_three.le hK' hnc' ⟨z, hzR, hzK, hzp, hzc⟩ hKs hKnab hiso φ hφs hY₀).elim
  ·
    have huniq' : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
        L = K' := fun L hL => hcfg.red.eq_of_forall_mem_center hK' hL hcent
    by_cases hKD' : HasKlingenData p Tbar
        (((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore p)))
    swap
    · exact (h3 p P' M N T Tbar hcfg K' hK' huniq' hnc' hcent hKD').elim
    by_cases hsp' : IsKlingenComponent p K'
    swap
    · exact (hother p P' M N T Tbar hcfg K' hK' huniq' hnc' hcent hKD' hsp').elim
    obtain ⟨d', hd'', ⟨e'⟩⟩ := hsp'
    have hp2 : p ≠ 2 := hcfg.loc.ne_two
    have hZ'c : Subgroup.center K' = ⊥ :=
      hmod.center K' p d' hp2 hd'' hK'.2.2 (hcfg.isPGroup_center hK') ⟨e'⟩
    have eK' : K' ≃* CatGroup d' :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ'c.symm)).trans
        e'
    have hC' := hcfg.centralizer_eq_bot hK' huniq' hcent hZ'c
    haveI hKn' : K'.Normal := normal_of_forall_isComponentOf_eq hK' huniq'
    have hOut' := hk.outer p hp2 d' hd'' K' ⟨eK'⟩
    have hRK'' : (Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤ K' := by
      have : Finite (MulAut K') := MulEquiv.finite_left
      intro x hx
      obtain ⟨n, hn⟩ := Tbar.isPGroup' ⟨x, hx⟩
      have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hmem := mem_sup_centralizer_of_pow hp hOut' hxn
      rwa [hC', sup_bot_eq] at hmem
    obtain ⟨hK's, hK'nab, hK'cat⟩ := hcfg.component_facts hK' hZ'c
    have hJK : J ≤ K' := by
      have := le_sup_centralizer_of_isPerfect hJper (hSch K' hK's hK'nab hK'cat) (K := K')
      rwa [hC', sup_bot_eq] at this
    have hRK : (Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ K' = Tbar :=
      inf_eq_left.mpr hRK''
    have hK'X : ¬ K' ≤ d1X0 p M N := by
      refine not_le_of_weakCore_le hp Tbar hcfg.red.weakCore_le hcfg.red.ne_top ?_
      rw [hRK, hcfg.pRank_rbar_eq_three]
    have hKK : K' ≤ Hyp111.d1KBar p M N := Hyp111.le_d1KBar hK' hK'X
    have hNT : Subgroup.normalizer
        (((Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ K' : Subgroup _) :
          Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N := by
      rw [hRK]
      refine (normalizer_le_weakCore p le_rfl ?_ ?_).trans hcfg.red.weakCore_le
      · rw [hcfg.pRank_rbar_eq_three]; norm_num
      · rw [hcfg.pRank_rbar_eq_three.symm]
        exact pRank_mono p hp le_sup_left
    have h93 : Hyp111.Hyp93At p M N := ⟨fun x hx => by
      obtain ⟨m, hm, k, hk', rfl⟩ := factor_of_normalizer_inf_le he hK' hNT x hx
      exact ⟨m, hm, k, hKK hk', rfl⟩, hcore⟩
    exact factor_of_le_d1KBar h93 hW hWK (noPPrime_of_simple hKs hKp) hκ
      (hWJ.le.trans (hJK.trans hKK)) hNH

theorem hyp917R_of_ext_of_rankTwo {P : Sylow p G} {M H R B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hext : D1Extremal p P M H R)
    (hBR : B ≤ R) (hidx : B.relIndex R ≤ p)
    (hNorm : ∀ U : Subgroup G, B ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M)
    (hR3 : Open.pRank p R ≤ 3) (h917 : Hyp917Ext p M H B K)
    (h2 : AGLRankTwoFactorAt p M H B K) : Hyp917R p M H B K := by
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  intro N hN hNM hBN hcov
  have hB : IsPGroup p B := hext.isPGroup.to_le hBR
  obtain ⟨T, hBT, hTN, hTM, hT, hmax⟩ :=
    exists_maxPSubgroup_of_normalizer_le hB hBN (hBR.trans hext.le_M) hNorm
  by_cases hTB : T = B
  · exact Or.inl (h2 N T hN hNM hBN hcov hBT hTN hTM hT hmax (Or.inl hTB))
  by_cases hrk : Open.pRank p T ≤ 2
  · exact Or.inl (h2 N T hN hNM hBN hcov hBT hTN hTM hT hmax (Or.inr hrk))
  push Not at hrk
  have hcard : Nat.card R ≤ Nat.card T := by
    have hmul := Subgroup.relIndex_mul_card (H := B) (K := R)
    rw [inf_of_le_left hBR] at hmul
    have hlt : Nat.card B < Nat.card T := lt_of_le_of_ne (Subgroup.card_le_of_le hBT)
      fun h => hTB (Subgroup.eq_of_le_of_card_ge hBT h.ge).symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hB
    rw [hn, ha] at hlt
    have han : a < n := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    have hpa : p * p ^ a ≤ p ^ n := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right hp.pos han
    calc Nat.card R = B.relIndex R * Nat.card B := hmul.symm
      _ ≤ p * Nat.card B := Nat.mul_le_mul_right _ hidx
      _ = p * p ^ a := by rw [ha]
      _ ≤ p ^ n := hpa
      _ = Nat.card T := hn.symm
  obtain ⟨P', hP'⟩ := exists_d1Extremal_of_maxPSubgroup hext hN hNM hTN hTM hT hmax hcard hrk
    (hR3.trans hrk)
  by_cases hlt : d1Kappa p M H < d1Kappa p M N
  · exact Or.inr hlt
  · exact Or.inl (h917 P' N T hP' hBT hcov (not_lt.mp hlt))

theorem exists_pElem_of_dvd [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] (h : p ∣ Nat.card Y) :
    ∃ x : Y, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  refine ⟨x, fun h1 => ?_, 1, by rw [pow_one, ← hx]; exact pow_orderOf_eq_one x⟩
  rw [h1, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

theorem D1OneSmall3Data.sq_dvd_card {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : D1OneSmall3Data p P M H R Rbar K) :
    p ^ 2 ∣ Nat.card K := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  set Xb := ((d1LiftX p H R K).subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := H) p))
  have hXp : IsPGroup p (d1LiftX p H R K) := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hXb : Xb ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, ⟨-, hzK⟩, hzy⟩ := Subgroup.mem_subgroupOf.mp hy
    have : z = y := Subtype.ext hzy
    exact this ▸ hzK
  have hnc : ¬ IsCyclic Xb :=
    not_isCyclic_map_of_isPGroup (d1LiftX_le_H p H R K) hXp hd.toCore.not_isCyclic_d1LiftX
  exact (sq_dvd_card_of_not_isCyclic (hXp.comap_subtype.map _) hnc).trans
    (Subgroup.card_dvd_of_le hXb)

theorem D1OneSmall3Data.not_hasPrimeConstraint {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : D1OneSmall3Data p P M H R Rbar K) :
    ∀ (P' : Sylow p G) (N T : Subgroup G), D1Extremal p P' M N T → AGLCovers p H N K →
      ¬ HasPrimeConstraint (G := N) p := by
  intro P' N T hP' hcov hc
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  obtain ⟨hKs, hKnab⟩ := hd.toCore.isSimpleGroup
  have hK2 := hd.sq_dvd_card
  exact D1Extremal.false_of_hasPrimeConstraint_of_cover hP' hc hKs hKnab
    (exists_pElem_of_dvd ((dvd_pow_self p two_ne_zero).trans hK2)) hcov hK2

theorem D1OneSmall3Data.hyp917R_native {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hd : D1OneSmall3Data p P M H R Rbar K) : Hyp917R p M H R K :=
  hd.hyp917R h3 hother hSch hk hmod hd.not_hasPrimeConstraint

theorem D1OneSmall3Data.hyp917Ext_native {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hd : D1OneSmall3Data p P M H R Rbar K) {B : Subgroup G}
    (hXB : d1LiftX p H R K ≤ B) : Hyp917Ext p M H B K :=
  hd.hyp917Ext h3 hother hSch hk hmod hd.not_hasPrimeConstraint hXB

end CFSG.LocalAnalysis.RankThreeTheoremC
