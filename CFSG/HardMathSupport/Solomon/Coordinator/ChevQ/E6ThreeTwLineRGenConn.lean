module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentTorus
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularCentralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSLineR

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen CFSG.LieType.Seitz

theorem pow_mem_of_mul_pow_eq_one {G : Type*} [Group G] {N : Subgroup G} {t r₀ : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hr₀ : r₀ ∈ N) {m : ℕ}
    (hm : (t * r₀) ^ m = 1) : t ^ m ∈ N := by
  have key : ∀ k : ℕ, ∃ n ∈ N, (t * r₀) ^ k = t ^ k * n := by
    intro k
    induction k with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨n, hn, hk⟩ := ih
      refine ⟨t⁻¹ * n * t * r₀, N.mul_mem ?_ hr₀, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) n).1 hn
        simpa only [inv_inv] using h
      · rw [pow_succ, hk, pow_succ]
        group
  obtain ⟨n, hn, hk⟩ := key m
  rw [hm] at hk
  rw [eq_inv_of_mul_eq_one_left hk.symm]
  exact N.inv_mem hn

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {M : Subgroup G} {t : G} {a b : ℕ}
    (hab : a.Coprime b) (ha : t ^ a ∈ M) (hb : t ^ b ∈ M) : t ∈ M := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have key : t = (t ^ a) ^ u * (t ^ b) ^ v := by
    rw [← zpow_natCast t a, ← zpow_natCast t b, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have h : (a : ℤ) * u + (b : ℤ) * v = 1 := by linarith [huv]
    rw [h, zpow_one]
  rw [key]
  exact M.mul_mem (M.zpow_mem ha u) (M.zpow_mem hb v)

theorem mem_of_mul_pow_eq_one {G : Type*} [Group G] {N : Subgroup G} {t r₀ : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hr₀ : r₀ ∈ N) {m : ℕ}
    (hm : (t * r₀) ^ m = 1) (hcop : m.Coprime (orderOf t)) : t ∈ N := by
  obtain ⟨k, hk'⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk']
  exact N.pow_mem (pow_mem_of_mul_pow_eq_one ht hr₀ hm) k

theorem mem_of_relIndex_dvd_three {G : Type*} [Group G] {J H : Subgroup G}
    (hnorm : ∀ c ∈ H, ∀ x ∈ J, c * x * c⁻¹ ∈ J) (hidx : J.relIndex H ∣ 3) {c : G}
    (hc : c ∈ H) {r m : ℕ} (hr : r.Coprime 3) (hcm : c ^ (r ^ m) = 1) : c ∈ J := by
  haveI : (J.subgroupOf H).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hnorm g g.2 x hx⟩
  have hpow : c ^ (J.relIndex H) ∈ J := by
    have h1 := Subgroup.pow_index_mem (J.subgroupOf H) (⟨c, hc⟩ : H)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h1
    exact h1
  have h3 : c ^ 3 ∈ J := by
    obtain ⟨d, hd⟩ := hidx
    rw [hd, pow_mul]
    exact J.pow_mem hpow d
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left m hr).symm h3
    (by rw [hcm]; exact J.one_mem)

section Conn

set_option linter.unusedSectionVars false


theorem coprime_orderOf_of_mem_torusGroup {τ : Tag} {L : Type} [Field L] {r : ℕ} [hr : Fact r.Prime]
    [CharP L r] {t : ModGL τ L} (ht : t ∈ torusGroup τ L) (h0 : orderOf t ≠ 0) (n : ℕ) :
    (r ^ n).Coprime (orderOf t) := by
  refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hr.out).2 fun hdvd => ?_)
  have hs : orderOf (t ^ (orderOf t / r)) = r := orderOf_pow_orderOf_div h0 hdvd
  have hsT : t ^ (orderOf t / r) ∈ torusGroup τ L := pow_mem ht _
  have hs1 : (t ^ (orderOf t / r)) ^ (r ^ 1) = 1 := by
    have h := pow_orderOf_eq_one (t ^ (orderOf t / r))
    rw [hs] at h
    rw [pow_one]
    exact h
  rw [eq_one_of_torus_pow_eq_one hsT hs1, orderOf_one] at hs
  exact hr.out.one_lt.ne hs

theorem mem_layer_of_connFixed {N : Set ℕ} (hN : ∀ n ∈ N, TwE6ConnFixed n)
    (hNsub : ∀ n ∈ N, n = 22 ∨ n = 30 ∨ n = 40) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {q : ℕ} {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hcube : TwE6Cube K σ q E) {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    {h : twistedE6InndiagGL K σ} (hh : twistedE6InndiagConj K σ h = f)
    (hdim : ∃ n ∈ N, twE6MatFixDim K σ h = 6 + n) {c : twistedE6RootGroup K σ}
    (hfc : f c = c) {m : ℕ} (hcm : c ^ (ringChar K ^ m) = 1) :
    c ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} := by
  classical
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hcube.three_dvd
    omega
  have hf3 : f ^ 3 = 1 := hcube.elemAbelian.2 f hfE
  have hinj := twE6_conj_injective K σ q hcube.frob hcube.card_field hq2
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hf3
  obtain ⟨e, heE, hne⟩ := exists_mem_not_mem_zpowers (E := E) hcube.card_E hf3
  have he1 : e ≠ 1 := fun h' => hne (h' ▸ one_mem _)
  obtain ⟨h', hh', -, hh'3⟩ := exists_matrix_lift_of_mem K σ q hcube.frob hcube.card_field hq2
    hcube.elemAbelian hcube.le_inndiag heE he1
  have hcomm : h * h' = h' * h := by
    apply hinj
    rw [map_mul, map_mul, hh, hh']
    exact congrArg Subtype.val (hcube.elemAbelian.1.is_comm.comm ⟨f, hfE⟩ ⟨e, heE⟩)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, ff, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hcube.card_field hq2
  have hK' : Nat.card K = (ringChar K ^ ff) ^ 2 := by rw [← hqf]; exact hcube.card_field
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ ff) := by intro c; rw [← hqf]; exact hcube.frob c
  have hpℓ : 3 ≠ ringChar K := fun h' => hcube.char_ne_three h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hdim3 : twE6MatFixDim K σ h = 28 ∨ twE6MatFixDim K σ h = 36 ∨
      twE6MatFixDim K σ h = 46 := by
    obtain ⟨n, hn, hn'⟩ := hdim
    rcases hNsub n hn with rfl | rfl | rfl <;> omega
  obtain ⟨S, a, b, ι, Fr, hDq, hFr, hΦ, haT, hbT, hap, hbp, ha1, hinjι, hrange, hca, hcb, hker⟩ :=
    exists_langSetup_pair_of_inndiag_twE6 hp hf hK' σ hσ' hcube.char_ne_three hp₀ hp₀ℓ hq₀ h h'
      hcomm hh3 hh'3 hh1 hdim3
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  have h3q' : 3 ∣ S.D.q + 1 := by rw [hDq, ← hqf]; exact hcube.three_dvd
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hDq]; exact hFr c
  have hk : (kernelRoots (rootCharHom a)).ncard ∈ N := by
    obtain ⟨n, hn, hn'⟩ := hdim
    have : (kernelRoots (rootCharHom a)).ncard = n := by omega
    rwa [this]
  have hq2' : S.D.q ≠ 2 := by rw [hDq, ← hqf]; exact hcube.ne_two
  have hcompfix : (fixedPoints (Subgroup.zpowers f)).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [← hh, ← fixSubgroup_eq_fixedPoints, map_fixSubgroup_eq_of_conj ι hinjι _ _ hca, hrange]
  have hcomp : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      CFSG.Open.IsComponentOf ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι)
        (fixedPoints (Subgroup.zpowers f)) := by
    intro i hq
    have hCd : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} ≤ ι.range := fun x hx => by
      rw [hrange]
      exact (Subgroup.mem_inf.1 hx).1
    have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}).comap ι =
        fixedPoints (Subgroup.zpowers f) := by
      rw [← hcompfix]
      exact Subgroup.comap_map_eq_self_of_injective hinjι _
    have hcompR : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) := by
      obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S haT i
      exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hq⟩
    have := isComponentOf_comap_of_injective ι hinjι (hcompR.1.trans hCd) hCd hcompR
    rwa [hcomapfix] at this
  set comps : Subgroup (twistedE6RootGroup K σ) :=
    sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} with hcomps
  have hA : (⨆ (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ comps.map ι := by
    refine iSup₂_le fun i hi => ?_
    have hRle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range := by
      rw [hrange]
      exact KSGen.rationalComponent_le_Γ S i
    calc rationalComponent S.ρ S.Γ (rootCharHom a) i =
        ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι :=
          (Subgroup.map_comap_eq_self hRle).symm
      _ ≤ comps.map ι := Subgroup.map_mono (le_sSup (hcomp i hi))
  have hcfix : c ∈ fixedPoints (Subgroup.zpowers f) := by
    have hle : Subgroup.zpowers f ≤ MulAction.stabilizer (MulAut (twistedE6RootGroup K σ)) c :=
      Subgroup.zpowers_le.2 hfc
    intro φ hφ
    exact hle hφ
  have hic : ι c ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [← hcompfix]
    exact ⟨c, hcfix, rfl⟩
  obtain ⟨hicΓ, hica⟩ := Subgroup.mem_inf.1 hic
  have hstab := e6_stab_le_kernelReflectionGroup_of_conn a hap (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hNsub _ hk)
  have hxM : ι c ∈ torusGroup Tag.E6 (AlgebraicClosure K) ⊔
      rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom a)) := by
    have h1 : ι c ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a :=
      Subgroup.mem_inf.2 ⟨KSGen.mem_adjointGroup_of_mem_Γ S hicΓ, hica⟩
    rw [toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 _ a hstab] at h1
    exact h1
  obtain ⟨t, -, htc, r₀, hr₀, hxt⟩ := hN _ hk (AlgebraicClosure K) p₀ S Fr hFr' hΦ hL3 h3q'
    hq2' a haT hap rfl (ι c) hxM (KSGen.step_eq_of_mem_Γ S hicΓ)
  have hr₀Γ : r₀ ∈ S.Γ :=
    (iSup₂_le fun i _ => KSGen.rationalComponent_le_Γ S i :
      (⨆ (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ S.Γ) hr₀
  have htΓ : t ∈ S.Γ := by
    have : t = ι c * r₀⁻¹ := by rw [hxt]; group
    rw [this]
    exact mul_mem hicΓ (inv_mem hr₀Γ)
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 1 := by
    by_contra hall
    push Not at hall
    exact ha1 (by rw [show a = 1 from funext hall]; exact rootDiagUnit_one)
  have hω : orderOf (a i₀) = 3 := orderOf_eq_prime (hap i₀) hi₀
  have htT : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) :=
    KSFourU.mem_torusGroup_of_commute_dV hω (KSGen.mem_adjointGroup_of_mem_Γ S htΓ)
      fun x => htc _ (rootDiagUnit_mem_torusGroup _)
  obtain ⟨r₁, hr₁, hr₁r⟩ := hA hr₀
  have hc₁ : ι (c * r₁⁻¹) = t := by
    rw [map_mul, map_inv, hr₁r, hxt]
    group
  have hcompsle : comps ≤ fixedPoints (Subgroup.zpowers f) := sSup_le fun _ hL => hL.1
  have hc₁fix : c * r₁⁻¹ ∈ fixedPoints (Subgroup.zpowers f) :=
    mul_mem hcfix (inv_mem (hcompsle hr₁))
  have hc₁N : c * r₁⁻¹ ∈ Subgroup.normalizer (comps : Set (twistedE6RootGroup K σ)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_rankThreeLayer _ hc₁fix
  have hord : orderOf (c * r₁⁻¹) = orderOf t := by
    rw [← hc₁]
    exact (orderOf_injective ι hinjι _).symm
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hcop : (ringChar K ^ m).Coprime (orderOf (c * r₁⁻¹)) := by
    rw [hord]
    refine coprime_orderOf_of_mem_torusGroup htT ?_ m
    rw [← hord]
    exact (isOfFinOrder_of_finite _).orderOf_pos.ne'
  have hc₁mem : c * r₁⁻¹ ∈ comps :=
    mem_of_mul_pow_eq_one hc₁N hr₁ (by rw [inv_mul_cancel_right]; exact hcm) hcop
  have hceq : c = c * r₁⁻¹ * r₁ := by rw [inv_mul_cancel_right]
  rw [hceq]
  exact mul_mem hc₁mem hr₁

end Conn

end KSLineR

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
