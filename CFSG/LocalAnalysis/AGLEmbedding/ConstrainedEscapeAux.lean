module

public import CFSG.LocalAnalysis.AGLEmbedding.IsolatedVertex
public import CFSG.LocalAnalysis.PreuniquenessRankFour.InvariantRankTwo
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Cyclic

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem card_le_of_isCyclic_of_forall_pow_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hp : 0 < p) (hC : ∀ c : C, c ^ p = 1) : Nat.card C ≤ p := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp (Monoid.exponent_dvd_of_forall_pow_eq_one hC)

theorem pRank_top_le_two_of_isCyclic_selfCentralizing (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    (hcyc : IsCyclic Q) : Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hEcard⟩ := PreuniquenessRankFour.Helpers.pRank_attained p hp (⊤ : Subgroup X)
  have hEp : ∀ e : E, e ^ p = 1 := fun e => Subtype.ext (by simpa using hE.2 e e.2)
  let φ : E →* MulAut Q := (MulAut.conjNormal (H := Q)).comp E.subtype
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hAut : IsCyclic (MulAut Q) := by
    have hunits := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
    rw [← hn] at hunits
    exact (IsCyclic.mulAutMulEquiv Q).isCyclic.mpr hunits
  have hrange : Nat.card φ.range ≤ p := by
    refine card_le_of_isCyclic_of_forall_pow_eq_one hp.pos ?_
    rintro ⟨_, e, rfl⟩
    exact Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hEp e, map_one, Subgroup.coe_one])
  have hkerQ : ∀ k : φ.ker, ((k : E) : X) ∈ Q := by
    intro k
    refine hQc (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
    have hfix := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : X)) (MonoidHom.mem_ker.mp k.2)
    change ((MulAut.conjNormal ((k : E) : X) ⟨q, hq⟩ : Q) : X) = q at hfix
    rw [MulAut.conjNormal_apply] at hfix
    calc q * ((k : E) : X) = ((k : E) : X) * q * ((k : E) : X)⁻¹ * ((k : E) : X) := by rw [hfix]
      _ = ((k : E) : X) * q := by group
  let ι : φ.ker →* Q :=
    { toFun := fun k => ⟨((k : E) : X), hkerQ k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab => by
    have hval := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext hval)
  have hkercyc : IsCyclic φ.ker := (MonoidHom.ofInjective hι).isCyclic.mpr inferInstance
  have hker : Nat.card φ.ker ≤ p :=
    card_le_of_isCyclic_of_forall_pow_eq_one hp.pos fun k => Subtype.ext (by
      rw [Subgroup.coe_pow, hEp, Subgroup.coe_one])
  have hcard : Nat.card E = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hle : p ^ Open.pRank p (⊤ : Subgroup X) ≤ p ^ 2 := by
    rw [← hEcard, hcard, sq]
    exact Nat.mul_le_mul hrange hker
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

theorem zpowers_normal_of_mem_centralizer {Q : Subgroup X} [Q.Normal]
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    (hcard : ∀ A : Subgroup X, A.Normal → IsElemAbelian p A → Nat.card A ≤ p) {x : X}
    (hx : x ∈ Subgroup.centralizer (Q : Set X)) (hxp : orderOf x = p) :
    (Subgroup.zpowers x).Normal := by
  have hcomm : ∀ a ∈ Subgroup.centralizer (Q : Set X), ∀ b ∈ Subgroup.centralizer (Q : Set X),
      a * b = b * a := fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a (hQc ha)
  let Ω : Subgroup X :=
    { carrier := {y | y ∈ Subgroup.centralizer (Q : Set X) ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        rw [(show Commute a b from hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨Subgroup.one_mem _, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩn : Ω.Normal := ⟨fun a ha g => ⟨(Subgroup.normal_centralizer (H := Q)).conj_mem a ha.1 g,
    by rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
  have hΩ : IsElemAbelian p Ω :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2.1 b b.2.1), fun y hy => hy.2⟩
  have hxΩ : Subgroup.zpowers x ≤ Ω :=
    Subgroup.zpowers_le.mpr ⟨hx, hxp ▸ pow_orderOf_eq_one x⟩
  have heq := Subgroup.eq_of_le_of_card_ge hxΩ (by
    rw [Nat.card_zpowers, hxp]
    exact hcard Ω hΩn hΩ)
  rw [heq]
  exact hΩn

end Cyclic

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem exists_isElemAbelian_normalizer_not_le (h : ReducedNongeneration p X R X₀)
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) :
    ∃ D : Subgroup X, D ≤ R ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
      ¬ Subgroup.normalizer (D : Set X) ≤ X₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hQR : Q ≤ R := hQ.le_sylow_of_normal R
  have hnc : ¬ IsCyclic Q := fun hcyc => by
    have h2 := pRank_top_le_two_of_isCyclic_selfCentralizing hp h.ne_two hQ hQc hcyc
    have h3 := h.three_le_pRank.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp le_top)
    omega
  obtain ⟨D₁, hD₁Q, hD₁n, hD₁, hD₁card⟩ :=
    odd_pGroup_normal_noncyclic_has_ambient_normal_elementary_rank_two p h.ne_two _
      R.isPGroup' (Q.subgroupOf R) inferInstance rfl
      (fun hcyc => hnc ((Subgroup.subgroupOfEquivOfLe hQR).isCyclic.mp hcyc))
  have hD₀Q : D₁.map (R : Subgroup X).subtype ≤ Q :=
    (Subgroup.map_mono hD₁Q).trans (Subgroup.map_subgroupOf_eq_of_le hQR).le
  have hRD₀ : (R : Subgroup X) ≤ Subgroup.normalizer
      ((D₁.map (R : Subgroup X).subtype : Subgroup X) : Set X) := by
    have hle := Subgroup.le_normalizer_map (H := D₁) (R : Subgroup X).subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hD₁n, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hle
  by_contra! hall
  apply h.not_normalClosure_le
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  obtain ⟨r, hr, hry⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hry
  have hN := hall ((D₁.map (R : Subgroup X).subtype).map (MulAut.conj c).toMonoidHom)
    (by
      rintro _ ⟨d, hd, rfl⟩
      exact hQR (‹Q.Normal›.conj_mem d (hD₀Q hd) c))
    (elementary_abelian_map p (elementary_abelian_map p hD₁ _) _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hD₁card])
  apply hN
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact ⟨r, hRD₀ hr, rfl⟩

end ReducedNongeneration

section Center

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem exists_mem_center_of_pRank_centralizer_le_two (hp : p.Prime) (hp2 : p ≠ 2)
    {P D : Subgroup G} (hP : IsPGroup p P) (hrank : 3 ≤ Open.pRank p P) (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hDP : D ≤ P)
    (hC : Open.pRank p (P ⊓ Subgroup.centralizer (D : Set G)) ≤ 2) :
    ∃ z : G, z ∈ D ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
        y ∈ Subgroup.zpowers z := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc := isCyclic_center_of_pRank_centralizer_le_two hp hp2 hP hrank hD hDcard hDP hC
  have hPnt : Nontrivial P := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    have hle := Subgroup.card_le_of_le hDP
    rw [Subgroup.card_bot, hDcard] at hle
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hZnt : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p
    (((hP.to_subgroup (Subgroup.center P)).card_eq_or_dvd).resolve_left Finite.one_lt_card.ne')
  have hzc : ((c : P) : G) ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩)
  have hzp : orderOf ((c : P) : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  refine ⟨(c : P), mem_of_mem_center_of_pRank_centralizer_le_two hp hD hDcard hDP hC (c : P).2
    hzc hzp, hzp, hzc, fun y hyc hyP hyp => ?_⟩
  let y' : Subgroup.center P := ⟨⟨y, hyP⟩, Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc g g.2)⟩
  have hy'p : orderOf y' = p := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hyp
  have heq : Subgroup.zpowers y' = Subgroup.zpowers c :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hy'p, hc])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers y')
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
    simpa using congrArg (fun w : Subgroup.center P => ((w : P) : G)) hk⟩

end Center

theorem normalizer_zpowers_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {M : Subgroup G} {z : G}
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (hC : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hN : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M := by
  intro n hn
  have hz' : n⁻¹ * z * n ∈ Subgroup.zpowers z := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) z).mp
      (Subgroup.mem_zpowers z)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
  have hconj : (P : Subgroup G).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxz : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp (hPz hx)
    have hcomm : x * (n⁻¹ * z * n) = n⁻¹ * z * n * x := hk ▸ (hxz.zpow_right k).eq
    rw [Subgroup.mem_centralizer_singleton_iff]
    change n * x * n⁻¹ * z = z * (n * x * n⁻¹)
    calc n * x * n⁻¹ * z = n * (x * (n⁻¹ * z * n)) * n⁻¹ := by group
      _ = n * (n⁻¹ * z * n * x) * n⁻¹ := by rw [hcomm]
      _ = z * (n * x * n⁻¹) := by group
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p P hPz hconj (P.isPGroup'.map _)
  have hcn : (c : G) * n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
    rintro _ ⟨x, hx, rfl⟩
    have hmem := hc ⟨n * x * n⁻¹, ⟨x, hx, rfl⟩, rfl⟩
    have heq : (c : G) * n * x * ((c : G) * n)⁻¹ = (c : G) * (n * x * n⁻¹) * (c : G)⁻¹ := by
      group
    change (c : G) * n * x * ((c : G) * n)⁻¹ ∈ (P : Subgroup G)
    rw [heq]
    exact hmem
  have hmem := M.mul_mem (M.inv_mem (hC c.2)) (hN hcn)
  rwa [inv_mul_cancel_left] at hmem

end CFSG.AGLEmbedding
