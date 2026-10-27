module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeHH
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeRestrict
import CFSG.RankThree.PartOne.FTL.Frattini
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.LocalAnalysis.GLTheoremA.S2019.Three CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

universe u

variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem commutator_eq_bot_of_commutator_commutator {G : Type*} [Group G] {T J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (h : ⁅⁅T, J⁆, J⁆ = ⊥) : ⁅T, J⁆ = ⊥ := by
  have h2 : ⁅⁅J, T⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm J T]
    exact h
  have h3 : ⁅⁅J, J⁆, T⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h
  rw [hJ] at h3
  rw [Subgroup.commutator_comm]
  exact h3

theorem conj_mem_commutator {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G))
    {c : G} (hc : c ∈ ⁅H, K⁆) : g * c * g⁻¹ ∈ ⁅H, K⁆ := by
  rw [Subgroup.commutator_def] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgH a).1 ha,
      g * b * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgK b).1 hb, ?_⟩
    rw [conjugate_commutatorElement]
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem iha

theorem normalizer_commutator {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_commutator hgH hgK hc, fun hc => ?_⟩
  have := conj_mem_commutator (inv_mem hgH) (inv_mem hgK) hc
  simpa [mul_assoc] using this

section Restrict

variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem commutator_fix_of_restrict {J T P : Subgroup (LinearMap.GeneralLinearGroup F V)}
    (W : Submodule F V) (hJp : ⁅J, J⁆ = J)
    (hJn : ∀ M : Subgroup (LinearMap.GeneralLinearGroup F V), M ≤ J →
      J ≤ Subgroup.normalizer (M : Set (LinearMap.GeneralLinearGroup F V)) →
      (∃ y ∈ P, y ≠ 1 ∧ y ∈ M) → M = J)
    (hJT : J ≤ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)))
    (hT2 : IsPGroup 2 T) (hPJ : P ≤ J) (hP3 : IsPGroup 3 P) (hP9 : 9 ≤ Nat.card P)
    (hPq : ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 →
      (((u : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hTW : T ≤ stabSub W) (hJW : J ≤ stabSub W)
    (IH : ∀ {J' T' P' : Subgroup (LinearMap.GeneralLinearGroup F W)}, ⁅J', J'⁆ = J' →
      (∀ M : Subgroup (LinearMap.GeneralLinearGroup F W), M ≤ J' →
        J' ≤ Subgroup.normalizer (M : Set (LinearMap.GeneralLinearGroup F W)) →
        (∃ y ∈ P', y ≠ 1 ∧ y ∈ M) → M = J') →
      J' ≤ Subgroup.normalizer (T' : Set (LinearMap.GeneralLinearGroup F W)) → IsPGroup 2 T' →
      P' ≤ J' → IsPGroup 3 P' → 9 ≤ Nat.card P' →
      (∀ u ∈ P', (∀ w ∈ P', u * w = w * u) → u ^ 3 = 1 →
        (((u : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) - 1) ^ 2 = 0) →
      ⁅T', J'⁆ = ⊥) :
    ∀ g ∈ ⁅T, J⁆, ∀ w ∈ W, ((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w := by
  classical
  set S := stabSub W with hS
  set r := restrictGL W with hr
  have hPS : P ≤ S := hPJ.trans hJW
  have hTJS : ⁅T, J⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro t ht j hj
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hTW ht) (hJW hj)) (inv_mem (hTW ht))) (inv_mem (hJW hj))
  have hfinal : ⁅(T.subgroupOf S).map r, (J.subgroupOf S).map r⁆ = ⊥ →
      ∀ g ∈ ⁅T, J⁆, ∀ w ∈ W, ((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w := by
    intro h g hg w hw
    have hgS := hTJS hg
    have h1 : r ⟨g, hgS⟩ ∈ ⁅(T.subgroupOf S).map r, (J.subgroupOf S).map r⁆ := by
      rw [← Subgroup.map_commutator, ← subgroupOf_commutator hTW hJW]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg)
    rw [h, Subgroup.mem_bot, restrictGL_eq_one_iff] at h1
    exact h1 w hw
  by_cases htriv : ∀ j ∈ J, ∀ w ∈ W, ((j : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w
  · apply hfinal
    have hJ'bot : (J.subgroupOf S).map r = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨j, hj, rfl⟩
      rw [Subgroup.mem_bot, restrictGL_eq_one_iff]
      exact htriv _ (Subgroup.mem_subgroupOf.1 hj)
    rw [hJ'bot, Subgroup.commutator_bot_right]
  push Not at htriv
  obtain ⟨j0, hj0, w0, hw0, hjw0⟩ := htriv
  let K : Subgroup (LinearMap.GeneralLinearGroup F V) :=
    { carrier := {k | k ∈ J ∧ ∀ w ∈ W, ((k : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w}
      mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun w hw => by
        rw [Units.val_mul, Module.End.mul_apply, hb.2 w hw, ha.2 w hw]⟩
      one_mem' := ⟨one_mem _, fun w _ => rfl⟩
      inv_mem' := fun {k} hk => ⟨inv_mem hk.1, fun w hw => by
        have h1 := hk.2 w hw
        calc ((k⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w
            = ((k⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V)
              (((k : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w) := by rw [h1]
          _ = w := by
            rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Module.End.one_apply]⟩ }
  have hKJ : K ≤ J := fun k hk => hk.1
  have hJK : J ≤ Subgroup.normalizer (K : Set (LinearMap.GeneralLinearGroup F V)) := by
    intro j hj
    have hconj : ∀ g ∈ J, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
      intro g hg k hk
      refine ⟨mul_mem (mul_mem hg hk.1) (inv_mem hg), fun w hw => ?_⟩
      have hgw : ((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w ∈ W := (hJW hg).2 w hw
      simp only [Units.val_mul, Module.End.mul_apply]
      rw [hk.2 _ hgw, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hconj j hj k hk, fun hk => ?_⟩
    have := hconj j⁻¹ (inv_mem hj) _ hk
    simpa [mul_assoc] using this
  have hinj : ∀ y ∈ P, ∀ (hy : y ∈ S), r ⟨y, hy⟩ = 1 → y = 1 := by
    intro y hyP hyS hry
    by_contra hy1
    have hyK : y ∈ K := ⟨hPJ hyP, (restrictGL_eq_one_iff W ⟨y, hyS⟩).1 hry⟩
    have hKeq := hJn K hKJ hJK ⟨y, hyP, hy1, hyK⟩
    have hj0K : j0 ∈ K := hKeq ▸ hj0
    exact hjw0 (hj0K.2 w0 hw0)
  have hinj' : ∀ a ∈ P, ∀ b ∈ P, ∀ (ha : a ∈ S) (hb : b ∈ S), r ⟨a, ha⟩ = r ⟨b, hb⟩ → a = b := by
    intro a haP b hbP ha hb h
    have h1 : r ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb⟩ = 1 := by
      have e : (⟨a⁻¹ * b, mul_mem (inv_mem ha) hb⟩ : S) = (⟨a, ha⟩ : S)⁻¹ * ⟨b, hb⟩ := rfl
      rw [e, map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hinj _ (mul_mem (inv_mem haP) hbP) _ h1
    rw [inv_mul_eq_one] at h2
    exact h2
  apply hfinal
  refine IH (P' := (P.subgroupOf S).map r) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rw [← Subgroup.map_commutator, ← subgroupOf_commutator hJW hJW, hJp]
  ·
    intro M' hM'J' hJ'M' hy'
    obtain ⟨y', hy'P', hy'1, hy'M'⟩ := hy'
    obtain ⟨⟨y, hyS⟩, hyP, rfl⟩ := hy'P'
    let M : Subgroup (LinearMap.GeneralLinearGroup F V) :=
      { carrier := {j | j ∈ J ∧ ∃ hj : j ∈ S, r ⟨j, hj⟩ ∈ M'}
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, ⟨mul_mem ha.2.1 hb.2.1, by
          have e : (⟨a * b, mul_mem ha.2.1 hb.2.1⟩ : S) = ⟨a, ha.2.1⟩ * ⟨b, hb.2.1⟩ := rfl
          rw [e, map_mul]
          exact mul_mem ha.2.2 hb.2.2⟩⟩
        one_mem' := ⟨one_mem _, ⟨one_mem _, by
          have e : (⟨1, one_mem S⟩ : S) = 1 := rfl
          rw [e, map_one]
          exact one_mem _⟩⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, ⟨inv_mem ha.2.1, by
          have e : (⟨a⁻¹, inv_mem ha.2.1⟩ : S) = (⟨a, ha.2.1⟩ : S)⁻¹ := rfl
          rw [e, map_inv]
          exact inv_mem ha.2.2⟩⟩ }
    have hMJ : M ≤ J := fun j hj => hj.1
    have hJM : J ≤ Subgroup.normalizer (M : Set (LinearMap.GeneralLinearGroup F V)) := by
      have hconj : ∀ g ∈ J, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
        intro g hg m hm
        obtain ⟨hmJ, hmS, hmM⟩ := hm
        refine ⟨mul_mem (mul_mem hg hmJ) (inv_mem hg), mul_mem (mul_mem (hJW hg) hmS)
          (inv_mem (hJW hg)), ?_⟩
        have e : (⟨g * m * g⁻¹, mul_mem (mul_mem (hJW hg) hmS) (inv_mem (hJW hg))⟩ : S) =
            ⟨g, hJW hg⟩ * ⟨m, hmS⟩ * (⟨g, hJW hg⟩ : S)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
        have hgJ' : r ⟨g, hJW hg⟩ ∈ (J.subgroupOf S).map r :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg)
        exact (Subgroup.mem_normalizer_iff.1 (hJ'M' hgJ') _).1 hmM
      intro j hj
      rw [Subgroup.mem_normalizer_iff]
      intro m
      refine ⟨fun hm => hconj j hj m hm, fun hm => ?_⟩
      have := hconj j⁻¹ (inv_mem hj) _ hm
      simpa [mul_assoc] using this
    have hyM : y ∈ M := ⟨hPJ (Subgroup.mem_subgroupOf.1 hyP), hyS, hy'M'⟩
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hy'1
      have e : (⟨1, hyS⟩ : S) = 1 := rfl
      rw [e, map_one]
    have hMeq := hJn M hMJ hJM ⟨y, Subgroup.mem_subgroupOf.1 hyP, hy1, hyM⟩
    refine le_antisymm hM'J' ?_
    rintro _ ⟨⟨j, hjS⟩, hj, rfl⟩
    have hjM : j ∈ M := hMeq.symm ▸ (Subgroup.mem_subgroupOf.1 hj)
    obtain ⟨-, hjS', hjM'⟩ := hjM
    exact hjM'
  ·
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map r)
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.1 (hJT (Subgroup.mem_subgroupOf.1 hj)) t)
  ·
    exact (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTW).symm).map r
  · exact Subgroup.map_mono fun p hp => Subgroup.mem_subgroupOf.2 (hPJ (Subgroup.mem_subgroupOf.1 hp))
  · exact (hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm).map r
  ·
    have hbij : Function.Bijective (r.subgroupMap (P.subgroupOf S)) := by
      refine ⟨fun a b hab => ?_, MonoidHom.subgroupMap_surjective _ _⟩
      have h1 : r a = r b := congrArg Subtype.val hab
      apply Subtype.ext
      apply Subtype.ext
      exact hinj' _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2) _ _ h1
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hP9
  ·
    rintro _ ⟨⟨u, huS⟩, huP, rfl⟩ huc hu3
    have huP' := Subgroup.mem_subgroupOf.1 huP
    have hucP : ∀ w ∈ P, u * w = w * u := by
      intro w hw
      have h1 := huc (r ⟨w, hPS hw⟩) (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hw))
      rw [← map_mul, ← map_mul] at h1
      exact hinj' _ (mul_mem huP' hw) _ (mul_mem hw huP') _ _ h1
    have hu3' : u ^ 3 = 1 := by
      have h1 : r (⟨u, huS⟩ ^ 3) = r 1 := by rw [map_pow, hu3, map_one]
      have := hinj' _ (pow_mem huP' 3) _ (one_mem P) (pow_mem huS 3) (one_mem S) h1
      exact this
    have hq := hPq u huP' hucP hu3'
    ext w
    have h1 := LinearMap.congr_fun hq (w : V)
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply] at h1 ⊢
    rw [Submodule.coe_sub, restrictGL_apply, Submodule.coe_sub, restrictGL_apply]
    simpa using h1

end Restrict

theorem core_three (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = d →
    ∀ {J T P : Subgroup (LinearMap.GeneralLinearGroup F V)}, ⁅J, J⁆ = J →
    (∀ M : Subgroup (LinearMap.GeneralLinearGroup F V), M ≤ J →
      J ≤ Subgroup.normalizer (M : Set (LinearMap.GeneralLinearGroup F V)) →
      (∃ y ∈ P, y ≠ 1 ∧ y ∈ M) → M = J) →
    J ≤ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)) → IsPGroup 2 T →
    P ≤ J → IsPGroup 3 P → 9 ≤ Nat.card P →
    (∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 →
      (((u : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) - 1) ^ 2 = 0) →
    ⁅T, J⁆ = ⊥ := by
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
  intro V _ _ _ hd J T P hJp hJn hJT hT2 hPJ hP3 hP9 hPq
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_generalLinearGroup (F := F) (V := V)
  have hrestr : ∀ W : Submodule F V, W ≠ ⊤ → ∀ {T : Subgroup (LinearMap.GeneralLinearGroup F V)},
      J ≤ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)) → IsPGroup 2 T →
      T ≤ stabSub W → J ≤ stabSub W → ∀ g ∈ ⁅T, J⁆, ∀ w ∈ W,
        ((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w := by
    intro W hW T hJT hT2 hTW hJW
    have hlt : Module.finrank F W < d := hd ▸ Submodule.finrank_lt hW
    exact commutator_fix_of_restrict W hJp hJn hJT hT2 hPJ hP3 hP9 hPq hTW hJW
      (fun hJ'p hJ'n hJ'T hT'2 hP'J' hP'3 hP'9 hP'q =>
        IHd _ hlt (V := W) rfl hJ'p hJ'n hJ'T hT'2 hP'J' hP'3 hP'9 hP'q)
  revert T
  suffices H : ∀ m : ℕ, ∀ T : Subgroup (LinearMap.GeneralLinearGroup F V), Nat.card T = m →
      J ≤ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)) → IsPGroup 2 T →
      ⁅T, J⁆ = ⊥ by
    intro T hJT hT2
    exact H _ T rfl hJT hT2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
  intro T hTm hJT hT2
  by_contra hne
  have hT0le : ⁅T, J⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro t ht j hj
    have h1 : j * t⁻¹ * j⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hJT hj) t⁻¹).1 (inv_mem ht)
    have e : ⁅t, j⁆ = t * (j * t⁻¹ * j⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ht h1
  have hJT0 : J ≤ Subgroup.normalizer
      ((⁅T, J⁆ : Subgroup (LinearMap.GeneralLinearGroup F V)) : Set _) := fun j hj =>
    normalizer_commutator (hJT hj) (Subgroup.le_normalizer hj)
  have hTeq : ⁅T, J⁆ = T := by
    by_contra hneq
    have hcard : Nat.card ↥⁅T, J⁆ < Nat.card T :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hT0le hneq)
    exact hne (commutator_eq_bot_of_commutator_commutator hJp
      (IHm _ (hTm ▸ hcard) _ rfl hJT0 (hT2.to_le hT0le)))
  have hTne : T ≠ ⊥ := fun h => hne (by rw [h, Subgroup.commutator_bot_left])
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hTne
  set N : Subgroup (LinearMap.GeneralLinearGroup F V) := (frattini ↥T).map T.subtype with hNdef
  have hNT : N ≤ T := by
    rw [hNdef]
    exact Subgroup.map_subtype_le _
  have hmemN : ∀ t (ht : t ∈ T), t ∈ N ↔ (⟨t, ht⟩ : ↥T) ∈ frattini ↥T := by
    intro t ht
    rw [hNdef, Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, hut⟩
      have : u = ⟨t, ht⟩ := Subtype.ext hut
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hNnorm : ∀ g ∈ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)),
      ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hn
    have hτ : T.normalizerMonoidHom ⟨g, hg⟩ f ∈ frattini ↥T := by
      have := (Subgroup.characteristic_iff_map_eq.1 (frattini_characteristic (G := ↥T)))
        (T.normalizerMonoidHom ⟨g, hg⟩)
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hf
    exact Subgroup.mem_map.2 ⟨_, hτ, rfl⟩
  have hNsq : ∀ t ∈ T, t * t ∈ N := fun t ht => by
    rw [hmemN _ (mul_mem ht ht)]
    have := sq_mem_frattini hT2 ⟨t, ht⟩
    rwa [pow_two] at this
  have hNne : N ≠ T := by
    intro h
    apply frattini_ne_top (P := ↥T)
    rw [eq_top_iff]
    intro f _
    exact (hmemN _ f.2).1 (by rw [h]; exact f.2)
  have hJN : J ≤ Subgroup.normalizer (N : Set (LinearMap.GeneralLinearGroup F V)) := fun j hj => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hNnorm j (hJT hj) n hn, fun hn => ?_⟩
    have := hNnorm j⁻¹ (inv_mem (hJT hj)) _ hn
    simpa [mul_assoc] using this
  have hNJbot : ⁅N, J⁆ = ⊥ :=
    IHm _ (hTm ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hNT hNne)) N rfl hJN (hT2.to_le hNT)
  have hNTle : ⁅N, T⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro n hn t ht
    have h1 := hNnorm t (Subgroup.le_normalizer ht) n⁻¹ (inv_mem hn)
    have e : ⁅n, t⁆ = n * (t * n⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hn h1
  have hTNbot : ⁅T, N⁆ = ⊥ := by
    have h1 : ⁅⁅J, N⁆, T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm J N, hNJbot, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅N, T⁆, J⁆ = ⊥ := le_bot_iff.1 (by
      rw [← hNJbot]
      exact Subgroup.commutator_mono hNTle le_rfl)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hTeq] at h3
  have hNcent : ∀ n ∈ N, ∀ t ∈ T, n * t = t * n := by
    intro n hn t ht
    have := Subgroup.commutator_mem_commutator ht hn
    rw [hTNbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hNJc : ∀ n ∈ N, ∀ j ∈ J, n * j = j * n := by
    intro n hn j hj
    have := Subgroup.commutator_mem_commutator hn hj
    rw [hNJbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  set z : LinearMap.GeneralLinearGroup F V := -1 with hzdef
  have hzc : ∀ g : LinearMap.GeneralLinearGroup F V, g * z = z * g := fun g => by
    rw [hzdef, mul_neg, mul_one, neg_mul, one_mul]
  have hz2 : z * z = 1 := by rw [hzdef, neg_mul_neg, mul_one]
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F 3] at h'
    omega
  have hz1 : z ≠ 1 := by
    intro h
    have hall : ∀ v : V, v = 0 := by
      intro v
      have h1 := congrArg (fun k : LinearMap.GeneralLinearGroup F V => (k : V →ₗ[F] V) v) h
      simp only [hzdef, Units.val_neg, Units.val_one, LinearMap.neg_apply, Module.End.one_apply]
        at h1
      have h2 : (2 : F) • v = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        exact neg_add_cancel v
      exact (smul_eq_zero.1 h2).resolve_left h2F
    apply hTne
    rw [eq_bot_iff]
    intro g _
    rw [Subgroup.mem_bot]
    apply Units.ext
    ext v
    rw [hall v, map_zero, map_zero]
  have hcomm : ∀ s ∈ T, ∀ t ∈ T, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ = z := by
    intro s hs t ht
    have hcN : ⁅s, t⁆ ∈ N := by
      have h1 := hNsq _ (mul_mem hs ht)
      have h2 := hNsq _ (inv_mem hs)
      have h3 := hNsq _ (inv_mem ht)
      have hc := hNcent _ h2 _ (inv_mem ht)
      have e : ⁅s, t⁆ = s * t * (s * t) * (s⁻¹ * s⁻¹) * (t⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        calc s * t * s⁻¹ * t⁻¹ = s * t * (s * t) * (t⁻¹ * (s⁻¹ * s⁻¹)) * t⁻¹ := by group
          _ = s * t * (s * t) * (s⁻¹ * s⁻¹ * t⁻¹) * t⁻¹ := by rw [← hc]
          _ = s * t * (s * t) * (s⁻¹ * s⁻¹) * (t⁻¹ * t⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem h1 h2) h3
    have hcc : ⁅s, t⁆ * ⁅s, t⁆ = 1 := by
      have e : ⁅s * s, t⁆ = s * ⁅s, t⁆ * s⁻¹ * ⁅s, t⁆ := by
        simp only [commutatorElement_def]
        group
      have hcs := hNcent _ hcN s hs
      rw [← hcs, mul_inv_cancel_right] at e
      rw [← e, commutatorElement_eq_one_iff_mul_comm]
      exact hNcent _ (hNsq s hs) t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hcz⟩ := hcon
    set c := ⁅s, t⁆ with hcdef
    have hstab : ∀ g : LinearMap.GeneralLinearGroup F V, c * g = g * c →
        g ∈ stabSub (LinearMap.ker ((c : V →ₗ[F] V) - 1)) ∧
          g ∈ stabSub (LinearMap.ker ((c : V →ₗ[F] V) + 1)) := by
      intro g hg
      have hgE : (c : V →ₗ[F] V) * (g : V →ₗ[F] V) = (g : V →ₗ[F] V) * (c : V →ₗ[F] V) := by
        rw [← Units.val_mul, hg, Units.val_mul]
      have hg' : c * g⁻¹ = g⁻¹ * c := ((show Commute c g from hg).inv_right).eq
      have hgE' : (c : V →ₗ[F] V) * ((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) =
          ((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) * (c : V →ₗ[F] V) := by
        rw [← Units.val_mul, hg', Units.val_mul]
      have key : ∀ (k : V →ₗ[F] V), (c : V →ₗ[F] V) * k = k * (c : V →ₗ[F] V) →
          (∀ w ∈ LinearMap.ker ((c : V →ₗ[F] V) - 1), k w ∈ LinearMap.ker ((c : V →ₗ[F] V) - 1)) ∧
          ∀ w ∈ LinearMap.ker ((c : V →ₗ[F] V) + 1), k w ∈ LinearMap.ker ((c : V →ₗ[F] V) + 1) := by
        intro k hk
        have hk' : ∀ v, (c : V →ₗ[F] V) (k v) = k ((c : V →ₗ[F] V) v) := fun v => by
          have := LinearMap.congr_fun hk v
          simpa only [Module.End.mul_apply] using this
        constructor
        · intro w hw
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hw ⊢
          rw [hk', ← map_sub, hw, map_zero]
        · intro w hw
          rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hw ⊢
          rw [hk', ← map_add, hw, map_zero]
      obtain ⟨h1, h2⟩ := key _ hgE
      obtain ⟨h3, h4⟩ := key _ hgE'
      exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    have hTW : ∀ g ∈ T, g ∈ stabSub (LinearMap.ker ((c : V →ₗ[F] V) - 1)) ∧
        g ∈ stabSub (LinearMap.ker ((c : V →ₗ[F] V) + 1)) := fun g hg =>
      hstab g (hNcent _ hcN g hg)
    have hJW : ∀ g ∈ J, g ∈ stabSub (LinearMap.ker ((c : V →ₗ[F] V) - 1)) ∧
        g ∈ stabSub (LinearMap.ker ((c : V →ₗ[F] V) + 1)) := fun g hg =>
      hstab g (hNJc _ hcN g hg)
    have hWp : LinearMap.ker ((c : V →ₗ[F] V) - 1) ≠ ⊤ := by
      intro h
      apply hc1
      apply Units.ext
      ext v
      have hv : v ∈ LinearMap.ker ((c : V →ₗ[F] V) - 1) := by rw [h]; exact Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      rw [hv, Units.val_one, Module.End.one_apply]
    have hWm : LinearMap.ker ((c : V →ₗ[F] V) + 1) ≠ ⊤ := by
      intro h
      apply hcz
      apply Units.ext
      ext v
      have hv : v ∈ LinearMap.ker ((c : V →ₗ[F] V) + 1) := by rw [h]; exact Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
        at hv
      rw [hv, hzdef, Units.val_neg, Units.val_one, LinearMap.neg_apply, Module.End.one_apply]
    have hfp := hrestr _ hWp hJT hT2 (fun g hg => (hTW g hg).1) (fun g hg => (hJW g hg).1)
    have hfm := hrestr _ hWm hJT hT2 (fun g hg => (hTW g hg).2) (fun g hg => (hJW g hg).2)
    apply hne
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact eq_one_of_fix_eigen h2F hcc (hfp g hg) (hfm g hg)
  have hFD : FormData T N z := ⟨hNT, hNcent, hNsq, hzc, hz2, hz1, hcomm⟩
  have hPT : ∀ y ∈ P, ∀ t ∈ T, y * t * y⁻¹ ∈ T := fun y hy t ht =>
    (Subgroup.mem_normalizer_iff.1 (hJT (hPJ hy)) t).1 ht
  refine false_of_pGroup hFD hP3 hP9 hPT (fun y hy n hn => hNnorm y (hJT (hPJ hy)) n hn) ?_
  intro y hyP hyc hy3 hy1
  have hyA : ActData T N y :=
    ⟨hy3, hPT y hyP, fun n hn => hNnorm y (hJT (hPJ hyP)) n hn,
      fun A hAT hAab hAy => commute_of_quadratic_three_of_abelian hy3 (hPq y hyP hyc hy3)
        (hT2.to_le hAT) hAab hAy⟩
  refine ⟨hyA, ?_⟩
  by_contra hmove
  push Not at hmove
  have hfix : ∀ t ∈ T, t⁻¹ * (y * t * y⁻¹) ∈ N := fun t ht => hyA.fix_of_forall hFD hmove ht
  have hyN : y ∈ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)) := hJT (hPJ hyP)
  have hyT : ∀ t ∈ T, y * t * y⁻¹ = t := by
    set τ := T.normalizerMonoidHom ⟨y, hyN⟩ with hτ
    have hτ3 : τ ^ 3 = 1 := by
      rw [hτ, ← map_pow]
      have : (⟨y, hyN⟩ : Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have htriv : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥T) τ = 1 := by
      ext q
      induction q using QuotientGroup.induction_on with
      | H t =>
        have e := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply
          (frattini ↥T) τ t
        rw [QuotientGroup.mk'_apply] at e
        rw [e, MulAut.one_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        have h1 := (hmemN _ (mul_mem (inv_mem t.2) (hPT y hyP _ t.2))).1 (hfix t t.2)
        have h2 := inv_mem h1
        convert h2 using 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        rfl
    have hτ1 := CFSG.RankThree.PartOne.FTL.eq_one_of_trivial_mod_frattini hT2 hτ3 (by norm_num) htriv
    intro t ht
    have := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : LinearMap.GeneralLinearGroup F V))
      hτ1
    exact this
  have hcent : ∀ g ∈ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup F V)),
      ∀ m ∈ Subgroup.centralizer (T : Set (LinearMap.GeneralLinearGroup F V)),
        g * m * g⁻¹ ∈ Subgroup.centralizer (T : Set (LinearMap.GeneralLinearGroup F V)) := by
    intro g hg m hm
    rw [Subgroup.mem_centralizer_iff] at hm ⊢
    intro t ht
    have ht' : g⁻¹ * t * g ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) t).1 ht
      rwa [inv_inv] at this
    have h1 := hm _ ht'
    calc t * (g * m * g⁻¹) = g * ((g⁻¹ * t * g) * m) * g⁻¹ := by group
      _ = g * (m * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = g * m * g⁻¹ * t := by group
  have hM := hJn (J ⊓ Subgroup.centralizer (T : Set (LinearMap.GeneralLinearGroup F V))) inf_le_left
    (fun j hj => by
      rw [Subgroup.mem_normalizer_iff]
      intro m
      refine ⟨fun hm => Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hj (Subgroup.mem_inf.1 hm).1)
        (inv_mem hj), hcent j (hJT hj) m (Subgroup.mem_inf.1 hm).2⟩, fun hm => ?_⟩
      have h1 := hcent j⁻¹ (inv_mem (hJT hj)) _ (Subgroup.mem_inf.1 hm).2
      have e : j⁻¹ * (j * m * j⁻¹) * j⁻¹⁻¹ = m := by group
      rw [e] at h1
      refine Subgroup.mem_inf.2 ⟨?_, h1⟩
      have := mul_mem (mul_mem (inv_mem hj) (Subgroup.mem_inf.1 hm).1) hj
      have e2 : j⁻¹ * (j * m * j⁻¹) * j = m := by group
      rwa [e2] at this)
    ⟨y, hyP, hy1, Subgroup.mem_inf.2 ⟨hPJ hyP, Subgroup.mem_centralizer_iff.2 fun t ht => by
      have := hyT t ht
      calc t * y = y * t * y⁻¹ * y := by rw [this]
        _ = y * t := by group⟩⟩
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hjM : j ∈ J ⊓ Subgroup.centralizer (T : Set (LinearMap.GeneralLinearGroup F V)) := by
    rw [hM]
    exact hj
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hjM).2 t ht).symm

theorem commute_of_commutator_mem_center {G : Type*} [Group G] {J₀ : Subgroup G}
    (hJ₀ : ⁅J₀, J₀⁆ = J₀) {y : G} (hy : y ∈ J₀) (h : ∀ j ∈ J₀, ⁅y, j⁆ ∈ Subgroup.center G) :
    ∀ j ∈ J₀, y * j = j * y := by
  let H : Subgroup G :=
    { carrier := {v | v ∈ J₀ ∧ ∀ j ∈ J₀, ⁅v, j⁆ ∈ Subgroup.center G}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun j hj => by
        have e : ⁅a * b, j⁆ = a * ⁅b, j⁆ * a⁻¹ * ⁅a, j⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, Subgroup.mem_center_iff.1 (hb.2 j hj) a, mul_inv_cancel_right]
        exact mul_mem (hb.2 j hj) (ha.2 j hj)⟩
      one_mem' := ⟨one_mem _, fun j _ => by simp [Subgroup.one_mem]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun j hj => by
        have hc : ⁅j, a⁆ ∈ Subgroup.center G := by
          rw [← commutatorElement_inv]
          exact inv_mem (ha.2 j hj)
        rw [commutatorElement_inv_left, Subgroup.mem_center_iff.1 hc a⁻¹, inv_mul_cancel_right]
        exact hc⟩ }
  have hHJ : ⁅H, J₀⁆ ≤ Subgroup.center G := by
    rw [Subgroup.commutator_le]
    intro v hv j hj
    exact hv.2 j hj
  have h1 : ⁅⁅H, J₀⁆, J₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro j _
    exact (Subgroup.mem_center_iff.1 (hHJ hc) j)
  have h2 : ⁅⁅J₀, H⁆, J₀⁆ = ⊥ := by
    rw [Subgroup.commutator_comm J₀ H]
    exact h1
  have h3 : ⁅⁅J₀, J₀⁆, H⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hJ₀] at h3
  intro j hj
  have := Subgroup.commutator_mem_commutator hj (show y ∈ H from ⟨hy, h⟩)
  rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this.symm

variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem commutator_eq_bot_of_quadratic_lift_three {S K : Type*} [Group S] [Group K] [Finite K]
    {J T : Subgroup S} (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJT : J ≤ Subgroup.normalizer (T : Set S)) (hT : IsPGroup 2 T)
    (π : K →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (ρ : K →* LinearMap.GeneralLinearGroup F V) (hρ : Function.Injective ρ)
    {J₀ P : Subgroup K} (hJ₀ : ⁅J₀, J₀⁆ = J₀) (hJ₀J : J₀.map π = J)
    (hPJ : P ≤ J₀) (hP : IsPGroup 3 P) (hP9 : 9 ≤ Nat.card P)
    (hPZ : ∀ u ∈ P, (∀ j ∈ J₀, u * j = j * u) → u = 1)
    (hPq : ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 →
      (((ρ u : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) - 1) ^ 2 = 0) :
    ⁅T, J⁆ = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite S := Finite.of_surjective π hπ
  have hQS : ∀ M : Subgroup K, M ≤ J₀ → J₀ ≤ Subgroup.normalizer (M : Set K) →
      (∃ y ∈ P, y ≠ 1 ∧ y ∈ M) → M = J₀ := by
    intro M hMJ hJM hy
    obtain ⟨y, hyP, hy1, hyM⟩ := hy
    have hMπ : M.map π ≤ J := hJ₀J ▸ Subgroup.map_mono hMJ
    have hn : ((M.map π).subgroupOf J).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨m, hm, hmn⟩ := hn
      obtain ⟨g₀, hg₀, hg₀g⟩ : ∃ g₀ ∈ J₀, π g₀ = g := by
        have : (g : S) ∈ J₀.map π := hJ₀J ▸ g.2
        obtain ⟨g₀, hg₀, h⟩ := this
        exact ⟨g₀, hg₀, h⟩
      refine ⟨g₀ * m * g₀⁻¹, (Subgroup.mem_normalizer_iff.1 (hJM hg₀) m).1 hm, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hg₀g, hmn]⟩
    by_cases htop : (M.map π).subgroupOf J = ⊤
    ·
      have hdec : ∀ a ∈ J₀, ∃ m ∈ M, m⁻¹ * a ∈ π.ker := by
        intro a ha
        have h1 : (⟨π a, hJ₀J ▸ Subgroup.mem_map_of_mem π ha⟩ : ↥J) ∈ (M.map π).subgroupOf J :=
          htop ▸ Subgroup.mem_top _
        obtain ⟨m, hm, hma⟩ := Subgroup.mem_subgroupOf.1 h1
        refine ⟨m, hm, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hma, inv_mul_cancel]
      refine le_antisymm hMJ ?_
      rw [← hJ₀, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨m₁, hm₁, hz₁⟩ := hdec a ha
      obtain ⟨m₂, hm₂, hz₂⟩ := hdec b hb
      have ea : a = m₁ * (m₁⁻¹ * a) := by group
      have eb : b = m₂ * (m₂⁻¹ * b) := by group
      rw [ea, eb, commutatorElement_mul_mul_of_central
        (fun w => Subgroup.mem_center_iff.1 (hker hz₁) w)
        (fun w => Subgroup.mem_center_iff.1 (hker hz₂) w)]
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hm₁ hm₂) (inv_mem hm₁)) (inv_mem hm₂)
    ·
      exfalso
      have hZ := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJq hn htop
      apply hy1
      refine hPZ y hyP (commute_of_commutator_mem_center hJ₀ (hPJ hyP) fun j hj => ?_)
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have hπy : (⟨π y, hJ₀J ▸ Subgroup.mem_map_of_mem π (hPJ hyP)⟩ : ↥J) ∈
          (M.map π).subgroupOf J := Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem π hyM)
      have := Subgroup.mem_center_iff.1 (hZ hπy) ⟨π j, hJ₀J ▸ Subgroup.mem_map_of_mem π hj⟩
      exact (congrArg Subtype.val this).symm
  set R : Subgroup K := T.comap π with hR
  have hπR : ∀ k : ↥R, π k ∈ T := fun k => k.2
  let πR : ↥R →* ↥T := (π.comp R.subtype).codRestrict T hπR
  have hπRs : Function.Surjective πR := by
    intro t
    obtain ⟨k, hk⟩ := hπ t
    exact ⟨⟨k, show π k ∈ T by rw [hk]; exact t.2⟩, Subtype.ext hk⟩
  haveI : Finite ↥T := inferInstance
  haveI hTnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hRker : πR.ker ≤ Subgroup.center ↥R := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    have hk' : (k : K) ∈ π.ker := by
      have := congrArg Subtype.val hk
      exact this
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hk') g)
  haveI : Group.IsNilpotent ↥R := isNilpotent_of_ker_le_center πR hRker
  obtain ⟨S₂⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  have hS₂char : (S₂ : Subgroup ↥R).Characteristic := Sylow.characteristic_of_normal S₂ inferInstance
  set Tt : Subgroup K := (S₂ : Subgroup ↥R).map R.subtype with hTt
  have hTt2 : IsPGroup 2 Tt := S₂.isPGroup'.map _
  have hTtT : Tt.map π = T := by
    have hmap := Sylow.coe_mapSurjective hπRs S₂
    have htop : ((S₂.mapSurjective hπRs : Sylow 2 ↥T) : Subgroup ↥T) = ⊤ :=
      ((S₂.mapSurjective hπRs).is_maximal' (hT.of_equiv Subgroup.topEquiv.symm) le_top).symm
    rw [hmap] at htop
    ext t
    constructor
    · rintro ⟨k, ⟨k', -, rfl⟩, rfl⟩
      exact k'.2
    · intro ht
      have : (⟨t, ht⟩ : ↥T) ∈ (S₂ : Subgroup ↥R).map πR := htop ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkt⟩ := this
      exact ⟨k, ⟨k, hk, rfl⟩, congrArg Subtype.val hkt⟩
  have hJ₀Tt : J₀ ≤ Subgroup.normalizer (Tt : Set K) := by
    intro j hj
    have hjR : j ∈ Subgroup.normalizer (R : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have hπj : π j ∈ J := hJ₀J ▸ Subgroup.mem_map_of_mem π hj
      have := Subgroup.mem_normalizer_iff.1 (hJT hπj) (π k)
      simp only [hR, Subgroup.mem_comap, map_mul, map_inv]
      exact this
    have hconj : ∀ g ∈ Subgroup.normalizer (R : Set K), ∀ x ∈ Tt, g * x * g⁻¹ ∈ Tt := by
      intro g hg x hx
      obtain ⟨x', hx', rfl⟩ := hx
      have := (Subgroup.characteristic_iff_map_eq.1 hS₂char) (R.normalizerMonoidHom ⟨g, hg⟩)
      rw [hTt, ← this]
      exact ⟨_, Subgroup.mem_map_of_mem _ hx', rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj j hjR x hx, fun hx => ?_⟩
    have := hconj j⁻¹ (inv_mem hjR) _ hx
    simpa [mul_assoc] using this
  have hcore : ⁅Tt.map ρ, J₀.map ρ⁆ = ⊥ := by
    refine core_three _ rfl (P := P.map ρ) ?_ ?_ ?_ (hTt2.map ρ) (Subgroup.map_mono hPJ)
      (hP.map ρ) ?_ ?_
    · rw [← Subgroup.map_commutator, hJ₀]
    · intro M' hM'J hJM' hy'
      obtain ⟨y', ⟨y, hyP, rfl⟩, hy'1, hy'M'⟩ := hy'
      have hMeq := hQS (M'.comap ρ ⊓ J₀) inf_le_right (fun j hj => by
          rw [Subgroup.mem_normalizer_iff]
          intro m
          have hρj : ρ j ∈ Subgroup.normalizer (M' : Set _) := hJM' (Subgroup.mem_map_of_mem ρ hj)
          constructor
          · intro hm
            refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hj (Subgroup.mem_inf.1 hm).2)
              (inv_mem hj)⟩
            rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
            exact (Subgroup.mem_normalizer_iff.1 hρj _).1 (Subgroup.mem_inf.1 hm).1
          · intro hm
            refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
            · have h1 := (Subgroup.mem_inf.1 hm).1
              rw [Subgroup.mem_comap, map_mul, map_mul, map_inv] at h1
              exact (Subgroup.mem_normalizer_iff.1 hρj _).2 h1
            · have := mul_mem (mul_mem (inv_mem hj) (Subgroup.mem_inf.1 hm).2) hj
              have e : j⁻¹ * (j * m * j⁻¹) * j = m := by group
              rwa [e] at this)
        ⟨y, hyP, fun h => hy'1 (by rw [h, map_one]), Subgroup.mem_inf.2 ⟨hy'M', hPJ hyP⟩⟩
      refine le_antisymm hM'J ?_
      rintro _ ⟨j, hj, rfl⟩
      have : j ∈ M'.comap ρ ⊓ J₀ := by rw [hMeq]; exact hj
      exact (Subgroup.mem_inf.1 this).1
    · exact le_trans (Subgroup.map_mono hJ₀Tt) (Subgroup.le_normalizer_map ρ)
    · rw [Subgroup.card_map_of_injective hρ]
      exact hP9
    · rintro _ ⟨u, huP, rfl⟩ huc hu3
      refine hPq u huP (fun w hw => hρ ?_) (hρ (by rw [map_pow, hu3, map_one]))
      rw [map_mul, map_mul]
      exact huc _ (Subgroup.mem_map_of_mem ρ hw)
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff_of_injective _ hρ] at hcore
  rw [← hTtT, ← hJ₀J, ← Subgroup.map_commutator, hcore, Subgroup.map_bot]

end CFSG.LocalAnalysis.GLTheoremA.S2019
