module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG

theorem subsingleton_of_fixed_eq_one_outside_zpowers {p : ℕ} [Fact p.Prime] {P V : Type*}
    [Group P] [Finite P] [Group V] [Finite V] [MulDistribMulAction P V]
    (hexp : ∀ g : P, g ^ p = 1) (hcard : p ^ 3 ≤ Nat.card P) (hV : ¬ p ∣ Nat.card V)
    {z : P} (hz : z ∈ Subgroup.center P)
    (hfix : ∀ g : P, g ∉ Subgroup.zpowers z → ∀ v : V, g • v = v → v = 1) :
    Subsingleton V := by
  classical
  have hZfix : ∀ v : V, z • v = v := by
    intro v
    by_cases hz1 : z = 1
    · rw [hz1, one_smul]
    have hzp : orderOf z = p := orderOf_eq_prime (hexp z) hz1
    have hzcard : Nat.card ↥(Subgroup.zpowers z) = p := by
      rw [Nat.card_zpowers, hzp]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hp3 : p < p ^ 3 := by
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by omega) hp1
      calc p = p * 1 := (mul_one p).symm
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hp2 (by omega)
        _ = p ^ 3 := by ring
    have hzlt : Nat.card ↥(Subgroup.zpowers z) < Nat.card P := by
      rw [hzcard]; exact lt_of_lt_of_le hp3 hcard
    have hne_top : Subgroup.zpowers z ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.card_top] at hzlt
      exact lt_irrefl _ hzlt
    obtain ⟨e, -, he⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne_top)
    set E : Subgroup P := Subgroup.closure ({e, z} : Set P) with hE
    have heE : e ∈ E := Subgroup.subset_closure (by simp)
    have hzE : z ∈ E := Subgroup.subset_closure (by simp)
    have hZle : Subgroup.zpowers z ≤ E := Subgroup.zpowers_le.mpr hzE
    have hZne : Subgroup.zpowers z ≠ E := by
      intro hEq
      exact he (hEq.symm ▸ heE)
    have hZlt : Subgroup.zpowers z < E := lt_of_le_of_ne hZle hZne
    have hcardlt : Nat.card ↥(Subgroup.zpowers z) < Nat.card ↥E := Subgroup.card_lt_of_lt hZlt
    have hcomm : ({e, z} : Set P).Pairwise Commute := by
      have h1 : Commute e z := Subgroup.mem_center_iff.mp hz e
      intro a ha b hb hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact h1
      · exact h1.symm
      · exact absurd rfl hab
    have hEexp : ∀ x : ↥E, x ^ p = 1 := by
      intro x
      apply Subtype.ext
      exact hexp (x : P)
    haveI : CFSG.IsElementaryAbelian p ↥E :=
      { toIsMulCommutative := Subgroup.isMulCommutative_closure hcomm
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hEexp }
    have hEp : IsPGroup p ↥E := CFSG.IsElementaryAbelian.isPGroup p ↥E
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
    have hplt : p < Nat.card ↥E := by
      rw [← hzcard]; exact hcardlt
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n ≤ 1 := by omega
      have hple : p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn1
      rw [pow_one] at hple
      rw [hn] at hplt
      exact absurd hple (not_le.mpr hplt)
    have hEcard : p ^ 2 ≤ Nat.card ↥E := by
      rw [hn]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn2
    letI : MulDistribMulAction ↥E V := MulDistribMulAction.compHom (A := V) E.subtype
    have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥E) (H := V)
      hEcard hV
    have hle : (⨆ (a : ↥E) (_ : a ≠ 1),
        CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) ≤
        CFSG.fixedPointSubgroup (Subgroup.zpowers z) V := by
      refine iSup₂_le fun a ha => ?_
      by_cases haz : (a : P) ∈ Subgroup.zpowers z
      · have ha1 : (a : P) ≠ 1 := fun h => ha (Subtype.ext h)
        have hap : orderOf (a : P) = p := orderOf_eq_prime (hexp (a : P)) ha1
        have hEq : Subgroup.zpowers (a : P) = Subgroup.zpowers z := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haz) ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hzp, hap]
        have hset : CFSG.fixedPointSubgroup (Subgroup.zpowers a) V =
            CFSG.fixedPointSubgroup (Subgroup.zpowers (a : P)) V := by
          ext w
          rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff,
            CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
          rfl
        rw [hset, hEq]
      · have hbot : CFSG.fixedPointSubgroup (Subgroup.zpowers a) V = ⊥ := by
          refine le_antisymm ?_ bot_le
          intro w hw
          rw [Subgroup.mem_bot]
          exact hfix (a : P) haz w
            ((CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a w).mp hw)
        rw [hbot]
        exact bot_le
    have htop : (⊤ : Subgroup V) ≤ CFSG.fixedPointSubgroup (Subgroup.zpowers z) V := by
      rw [← hgen]
      exact hle
    exact (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff (A := P) z v).mp
      (htop (Subgroup.mem_top v))
  by_contra hsub
  have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
  let φ : P →* MulAut V := MulDistribMulAction.toMulAut P V
  have hφ_smul : ∀ (g : P) (w : V), (φ g) • w = g • w := by
    intro g w
    rw [MulAut.smul_def, MulDistribMulAction.toMulAut_apply,
      MulDistribMulAction.toMulEquiv_apply]
  have hzker : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply, ← MulAut.smul_def, hφ_smul]
    exact hZfix w
  have hker : φ.ker ≤ Subgroup.zpowers z := by
    intro g hg
    by_contra hg'
    have hall : ∀ w : V, w = 1 := by
      intro w
      apply hfix g hg' w
      have h1 : (φ g) • w = w := by
        rw [MonoidHom.mem_ker.mp hg]
        exact one_smul (MulAut V) w
      rwa [hφ_smul] at h1
    exact hsub ⟨fun w w' => (hall w).trans (hall w').symm⟩
  have hkercard : Nat.card ↥φ.ker ≤ p := by
    have hdvd : Nat.card ↥φ.ker ∣ p := by
      have h1 := Subgroup.card_dvd_of_le hker
      rw [Nat.card_zpowers] at h1
      exact h1.trans (orderOf_dvd_of_pow_eq_one (hexp z))
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
    · rw [h]; exact (Fact.out : p.Prime).one_lt.le
    · rw [h]
  have hQcard : p ^ 2 ≤ Nat.card ↥φ.range := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    have h1 : p ^ 3 ≤ Nat.card ↥φ.ker * Nat.card ↥φ.range := by
      rw [hmul]; exact hcard
    have h2 : Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ p * Nat.card ↥φ.range :=
      Nat.mul_le_mul_right _ hkercard
    have h3 : p * p ^ 2 ≤ p * Nat.card ↥φ.range := by
      rw [← pow_succ']
      exact h1.trans h2
    exact Nat.le_of_mul_le_mul_left h3 (Fact.out : p.Prime).pos
  have hrange_exp : ∀ q : ↥φ.range, q ^ p = 1 := by
    intro q
    apply Subtype.ext
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp q.2
    show (q : MulAut V) ^ p = 1
    rw [← hg, ← map_pow, hexp g, map_one]
  have hQp : IsPGroup p ↥φ.range := by
    apply IsPGroup.of_exponent_dvd_pow (n := 1)
    rw [pow_one]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hrange_exp
  have hdvd : p ^ 2 ∣ Nat.card ↥φ.range := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    have hp2lt : p < p ^ 2 := by
      have h2 : 1 < p := (Fact.out : p.Prime).one_lt
      calc p = p * 1 := (mul_one p).symm
        _ < p * p := Nat.mul_lt_mul_of_pos_left h2 (by omega)
        _ = p ^ 2 := by ring
    have hplt : p < p ^ n := by rw [← hn]; exact lt_of_lt_of_le hp2lt hQcard
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n ≤ 1 := by omega
      have hple : p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn1
      rw [pow_one] at hple
      exact absurd hple (not_le.mpr hplt)
    refine ⟨p ^ (n - 2), ?_⟩
    rw [hn, ← pow_add]
    congr 1
    omega
  obtain ⟨E', hE'card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥φ.range) p (n := 2) hdvd
  have hE'exp : ∀ x : ↥E', x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact hrange_exp (x : ↥φ.range)
  haveI : CFSG.IsElementaryAbelian p ↥E' :=
    { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hE'card
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hE'exp }
  letI : MulDistribMulAction ↥E' V :=
    MulDistribMulAction.compHom (A := V) (φ.range.subtype.comp E'.subtype)
  have hgen' := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥E') (H := V)
    (by rw [hE'card]) hV
  have hbot : (⨆ (a : ↥E') (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun a ha => ?_
    intro w hw
    rw [Subgroup.mem_bot]
    have ha1 : (a : ↥φ.range) ≠ 1 := by
      intro h
      exact ha (Subtype.ext h)
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp ((a : ↥φ.range).2)
    have hg1 : φ g ≠ 1 := by
      rw [hg]
      intro h
      exact ha1 (Subtype.ext h)
    have hgz : g ∉ Subgroup.zpowers z := fun hmem =>
      hg1 (MonoidHom.mem_ker.mp ((Subgroup.zpowers_le.mpr hzker) hmem))
    apply hfix g hgz w
    have hwa : a • w = w := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a w).mp hw
    calc g • w = (φ g) • w := (hφ_smul g w).symm
      _ = (φ g) w := MulAut.smul_def _ _
      _ = ((a : ↥φ.range) : MulAut V) w := by rw [hg]
      _ = w := hwa
  have hcontr : (⊤ : Subgroup V) = ⊥ := by rw [← hgen', hbot]
  apply hsub
  refine ⟨fun w w' => ?_⟩
  have hw : w = 1 := Subgroup.mem_bot.mp (hcontr ▸ Subgroup.mem_top w)
  have hw' : w' = 1 := Subgroup.mem_bot.mp (hcontr ▸ Subgroup.mem_top w')
  rw [hw, hw']

theorem eq_top_of_fixed_le_outside_zpowers {p : ℕ} [Fact p.Prime] {P V : Type*}
    [Group P] [Finite P] [Group V] [Finite V] [MulDistribMulAction P V]
    (hexp : ∀ g : P, g ^ p = 1) (hcard : p ^ 3 ≤ Nat.card P) (hV : ¬ p ∣ Nat.card V)
    {z : P} (hz : z ∈ Subgroup.center P) (N : Subgroup V) [N.Normal]
    (hN : ∀ (g : P) (v : V), v ∈ N → g • v ∈ N)
    (hfix : ∀ g : P, g ∉ Subgroup.zpowers z → ∀ v : V, g • v = v → v ∈ N) :
    N = ⊤ := by
  classical
  have hNinv : CFSG.IsInvariant P V N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem hN
  letI : MulDistribMulAction P (V ⧸ N) :=
    CFSG.quotientMulDistribMulAction (A := P) (G := V) N hNinv
  letI : MulAction.QuotientAction P N := CFSG.quotientAction_of_isInvariant (A := P) N hNinv
  have hVq : ¬ p ∣ Nat.card (V ⧸ N) :=
    fun h => hV (h.trans (Subgroup.card_quotient_dvd_card N))
  have hNp : ¬ p ∣ Nat.card ↥N :=
    fun h => hV (h.trans (Subgroup.card_subgroup_dvd_card N))
  have hfix' : ∀ g : P, g ∉ Subgroup.zpowers z → ∀ q : V ⧸ N, g • q = q → q = 1 := by
    intro g hg q hq
    obtain ⟨v₀, hv₀⟩ := QuotientGroup.mk_surjective q
    set S : Set V := {x | (x : V ⧸ N) = q} with hS
    have hSinv : ∀ a : ↥(Subgroup.zpowers g), ∀ x ∈ S, (a : P) • x ∈ S := by
      intro a x hx
      have hxq : (x : V ⧸ N) = q := by simpa [hS] using hx
      have hqfix : (a : P) • q = q := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
        rw [← hk]
        exact MulAction.mem_fixedBy.mp
          (MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr hq) k)
      rw [hS, Set.mem_setOf_eq]
      rw [← MulAction.Quotient.smul_coe N (a : P) x, hxq]
      exact hqfix
    letI : MulAction ↥(Subgroup.zpowers g) S :=
      { smul := fun a x => ⟨(a : P) • (x : V), hSinv a x x.2⟩
        one_smul := fun x => Subtype.ext (by
          change ((1 : ↥(Subgroup.zpowers g)) : P) • (x : V) = (x : V)
          rw [Subgroup.coe_one, one_smul])
        mul_smul := fun a b x => Subtype.ext (by
          change (((a * b : ↥(Subgroup.zpowers g)) : P) • (x : V)) =
            ((a : P) • ((b : P) • (x : V)))
          rw [Subgroup.coe_mul, mul_smul]) }
    have hcardS : Nat.card S = Nat.card ↥N := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun x => ⟨(x : V) / v₀, ?_⟩
          invFun := fun n => ⟨(n : V) * v₀, ?_⟩
          left_inv := fun x => Subtype.ext (by
            show (x : V) / v₀ * v₀ = (x : V)
            exact div_mul_cancel _ _)
          right_inv := fun n => Subtype.ext (by
            show (n : V) * v₀ / v₀ = (n : V)
            exact mul_div_cancel_right _ _) }
      · exact (QuotientGroup.eq_iff_div_mem).mp (x.2.trans hv₀.symm)
      · show ((n : V) * v₀ : V ⧸ N) = q
        rw [(QuotientGroup.eq_one_iff (n : V)).mpr n.2, one_mul, hv₀]
    have hSp : ¬ p ∣ Nat.card S := by
      rw [hcardS]; exact hNp
    have hgp : IsPGroup p ↥(Subgroup.zpowers g) := by
      have hdvd : Nat.card ↥(Subgroup.zpowers g) ∣ p := by
        rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one (hexp g)
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h]; simp)
      · exact IsPGroup.of_card (n := 1) (by rw [h]; simp)
    obtain ⟨⟨c, hcS⟩, hcfix⟩ := hgp.nonempty_fixed_point_of_prime_not_dvd_card S hSp
    have hgc : g • c = c := by
      have h1 := hcfix ⟨g, Subgroup.mem_zpowers g⟩
      exact congrArg Subtype.val h1
    have hcN : c ∈ N := hfix g hg c hgc
    have hcq : (c : V ⧸ N) = 1 := (QuotientGroup.eq_one_iff c).mpr hcN
    exact hcS.symm.trans hcq
  haveI : Subsingleton (V ⧸ N) :=
    subsingleton_of_fixed_eq_one_outside_zpowers (p := p) (P := P) (V := V ⧸ N) hexp hcard hVq hz
      hfix'
  rw [Subgroup.eq_top_iff']
  intro v
  have hv1 : (v : V ⧸ N) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff v).mp hv1

theorem le_of_centralizer_le_outside_zpowers {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {P X Y : Subgroup G} (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hPY : P ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ p ∣ Nat.card Y) (hexp : ∀ g ∈ P, g ^ p = 1) (hcard : p ^ 3 ≤ Nat.card P)
    {z : G} (hzP : z ∈ P) (hz : ∀ g ∈ P, g * z = z * g)
    (hfix : ∀ g ∈ P, g ∉ Subgroup.zpowers z → Y ⊓ Subgroup.centralizer {g} ≤ X) :
    Y ≤ X := by
  classical
  haveI hPYnorm : Subgroup.Normalizes P Y := ⟨hPY⟩
  have hexp' : ∀ g : ↥P, g ^ p = 1 := by
    intro g
    apply Subtype.ext
    exact hexp (g : G) g.2
  have hz' : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hz (g : G) g.2
  have hN : ∀ (g : ↥P) (v : ↥Y), v ∈ X.subgroupOf Y → g • v ∈ X.subgroupOf Y := by
    intro g v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hPX g.2) (v : G)).mp hv
  have hfix' : ∀ g : ↥P, g ∉ Subgroup.zpowers (⟨z, hzP⟩ : ↥P) →
      ∀ v : ↥Y, g • v = v → v ∈ X.subgroupOf Y := by
    intro g hg v hv
    have hg' : (g : G) ∉ Subgroup.zpowers z := by
      intro hmem
      apply hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, by apply Subtype.ext; simpa using hk⟩
    have hconj : (g : G) * (v : G) * (g : G)⁻¹ = (v : G) := by
      simpa using congrArg Subtype.val hv
    have hcent : (v : G) ∈ Subgroup.centralizer ({(g : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (v : G) * (g : G) = ((g : G) * (v : G) * (g : G)⁻¹) * (g : G) := by rw [hconj]
        _ = (g : G) * (v : G) := by group
    have hmemX : (v : G) ∈ X :=
      hfix (g : G) g.2 hg' (Subgroup.mem_inf.mpr ⟨v.2, hcent⟩)
    rwa [Subgroup.mem_subgroupOf]
  haveI hNY : (X.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYX
  have htop := eq_top_of_fixed_le_outside_zpowers (p := p) (P := ↥P) (V := ↥Y)
    hexp' hcard hY hz' (X.subgroupOf Y) hN hfix'
  rw [Subgroup.subgroupOf_eq_top] at htop
  exact htop

end CFSG

end
