module

public import CFSG.Holt.H78.Sec4Toolkit
public import CFSG.Holt.H78.Lemma27Blocks
import CFSG.Holt.H78.Sec4CCL
import CFSG.Holt.H78.Sec4Known
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv
open scoped Pointwise

namespace P49S7

section PiQuotient

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ k, Group (H k)]
  {P : ∀ k, Subgroup (H k)}

@[expose] def piSingleHom (P : ∀ k, Subgroup (H k)) (k : ι) : P k →* Subgroup.pi Set.univ P :=
  ((MonoidHom.mulSingle H k).comp (P k).subtype).codRestrict _ fun x =>
    (Subgroup.mem_pi _).mpr fun j _ => by
      rcases eq_or_ne j k with rfl | hj
      · simp
      · simp [Pi.mulSingle_eq_of_ne hj]

@[simp] theorem coe_piSingleHom (k : ι) (x : P k) :
    (piSingleHom P k x : ∀ k, H k) = Pi.mulSingle k (x : H k) := rfl

theorem eq_one_of_forall_mem {N : Type*} [Group N] {ψ : Subgroup.pi Set.univ P →* N}
    (s : Finset ι) (hs : ∀ k ∈ s, ∀ x : P k, ψ (piSingleHom P k x) = 1)
    (e : Subgroup.pi Set.univ P) (he : ∀ k ∉ s, (e : ∀ k, H k) k = 1) : ψ e = 1 := by
  induction s using Finset.induction_on generalizing e with
  | empty =>
    have : e = 1 := Subtype.ext (funext fun k => he k (Finset.notMem_empty k))
    rw [this, map_one]
  | insert k s hk ih =>
    have hek : (e : ∀ k, H k) k ∈ P k := (Subgroup.mem_pi _).mp e.2 k trivial
    set x : P k := ⟨_, hek⟩
    have h1 := ih (fun j hj x => hs j (Finset.mem_insert_of_mem hj) x)
      (e * (piSingleHom P k x)⁻¹) fun j hj => by
        rcases eq_or_ne j k with rfl | hjk
        · simp [x]
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_piSingleHom, Pi.mul_apply,
            Pi.inv_apply, Pi.mulSingle_eq_of_ne hjk, inv_one, mul_one]
          exact he j (by simp [hjk, hj])
    rw [map_mul, map_inv, hs k (Finset.mem_insert_self k s) x, inv_one, mul_one] at h1
    exact h1

theorem conj_piSingleHom (e : Subgroup.pi Set.univ P) (k : ι) (x : P k) :
    e * piSingleHom P k x * e⁻¹ = piSingleHom P k
      (⟨(e : ∀ k, H k) k, (Subgroup.mem_pi _).mp e.2 k trivial⟩ * x *
        (⟨(e : ∀ k, H k) k, (Subgroup.mem_pi _).mp e.2 k trivial⟩)⁻¹) := by
  apply Subtype.ext
  funext j
  rcases eq_or_ne j k with rfl | hj
  · simp
  · simp [Pi.mulSingle_eq_of_ne hj]

theorem exists_coord_of_surjective [Fintype ι] {N : Type*} [Group N] [IsSimpleGroup N]
    (hN : ∃ a b : N, a * b ≠ b * a) {ψ : Subgroup.pi Set.univ P →* N}
    (hψ : Function.Surjective ψ) :
    ∃ k₀, (∀ e : Subgroup.pi Set.univ P, (e : ∀ k, H k) k₀ = 1 → ψ e = 1) ∧
      ∀ n : N, ∃ x : P k₀, ψ (piSingleHom P k₀ x) = n := by
  set S : ι → Subgroup N := fun k => (ψ.comp (piSingleHom P k)).range with hS
  have hnormal : ∀ k, (S k).Normal := fun k => ⟨by
    rintro _ ⟨x, rfl⟩ n
    obtain ⟨e, rfl⟩ := hψ n
    refine ⟨⟨(e : ∀ k, H k) k, (Subgroup.mem_pi _).mp e.2 k trivial⟩ * x *
      (⟨(e : ∀ k, H k) k, (Subgroup.mem_pi _).mp e.2 k trivial⟩)⁻¹, ?_⟩
    rw [MonoidHom.comp_apply, ← conj_piSingleHom, map_mul, map_mul, map_inv]
    rfl⟩
  have hcomm : ∀ k j, k ≠ j → ∀ x : P k, ∀ y : P j,
      ψ (piSingleHom P k x) * ψ (piSingleHom P j y) =
        ψ (piSingleHom P j y) * ψ (piSingleHom P k x) := by
    intro k j hkj x y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Pi.mulSingle_commute hkj (x : H k) (y : H j))
  have htop : ∃ k₀, S k₀ = ⊤ := by
    by_contra hne
    push Not at hne
    have hbot : ∀ k, S k = ⊥ := fun k => by
      have := hnormal k
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (S k)).resolve_right (hne k)
    obtain ⟨a, b, hab⟩ := hN
    have h1 : ∀ n : N, n = 1 := fun n => by
      obtain ⟨e, rfl⟩ := hψ n
      refine eq_one_of_forall_mem Finset.univ (fun k _ x => ?_) e fun k hk => absurd
        (Finset.mem_univ k) hk
      have : ψ (piSingleHom P k x) ∈ S k := ⟨x, rfl⟩
      rwa [hbot k, Subgroup.mem_bot] at this
    exact hab (by rw [h1 a, h1 b])
  obtain ⟨k₀, hk₀⟩ := htop
  have hbot : ∀ k, k ≠ k₀ → ∀ x : P k, ψ (piSingleHom P k x) = 1 := by
    intro k hk x
    have := hnormal k
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S k) with h | h
    · have : ψ (piSingleHom P k x) ∈ S k := ⟨x, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    · exfalso
      obtain ⟨a, b, hab⟩ := hN
      obtain ⟨x, hx⟩ : a ∈ S k := h ▸ Subgroup.mem_top a
      obtain ⟨y, hy⟩ : b ∈ S k₀ := hk₀ ▸ Subgroup.mem_top b
      exact hab (by rw [← hx, ← hy]; exact hcomm k k₀ hk x y)
  refine ⟨k₀, fun e he => eq_one_of_forall_mem (Finset.univ.erase k₀)
    (fun k hk x => hbot k (Finset.ne_of_mem_erase hk) x) e fun k hk => ?_, fun n => ?_⟩
  · have : k = k₀ := by
      by_contra h
      exact hk (Finset.mem_erase.mpr ⟨h, Finset.mem_univ k⟩)
    rw [this]
    exact he
  · obtain ⟨x, hx⟩ : n ∈ S k₀ := hk₀ ▸ Subgroup.mem_top n
    exact ⟨x, hx⟩

end PiQuotient

theorem closure_orderOf_eq_two_eq_top {M : Type*} [Group M] [IsSimpleGroup M] {x : M}
    (hx : orderOf x = 2) : Subgroup.closure {y : M | orderOf y = 2} = ⊤ := by
  have hconj : Group.conjugatesOfSet {y : M | orderOf y = 2} ⊆ {y : M | orderOf y = 2} := by
    intro z hz
    obtain ⟨a, ha, c, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    exact (SemiconjBy.orderOf_eq _ hc).symm.trans ha
  have hle : Subgroup.normalClosure {y : M | orderOf y = 2} ≤
      Subgroup.closure {y : M | orderOf y = 2} := Subgroup.closure_mono hconj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure {y : M | orderOf y = 2}) with h | h
  · have hx1 : x ∈ (⊥ : Subgroup M) := h ▸ Subgroup.subset_normalClosure hx
    rw [Subgroup.mem_bot] at hx1
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · exact eq_top_iff.mpr (h ▸ hle)

theorem exists_mem_pairProducts_apply_eq {Δ : Type*} [Finite Δ] {N : Subgroup (Perm Δ)}
    {a b c c' : Δ} (hc : c ∈ holtDelta N Δ a b) (hc' : c' ∈ holtDelta N Δ a b) :
    ∃ e ∈ pairProducts N a b, e c = c' := by
  obtain ⟨x, hx, hxc⟩ := mem_holtDelta_subgroup_perm_iff.mp hc
  obtain ⟨x', hx', hx'c⟩ := mem_holtDelta_subgroup_perm_iff.mp hc'
  exact ⟨_, pow_mem (mul_mem_pairProducts hx hx') _,
    pow_period_div_two_mul_smul_eq (G := Perm Δ) (Ω := Δ) ⟨hx.2.1, hxc⟩ ⟨hx'.2.1, hx'c⟩⟩

section Coordinate

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X] (D : HoltData K X)

theorem exists_coord_kill {a b : X} (hne : (longInvSwap K X a b).Nonempty)
    {Z : Type*} [Finite Z] {N : Subgroup (Perm Z)} [IsSimpleGroup N]
    (hN : ∃ x y : N, x * y ≠ y * x) (h2 : 2 ∣ Nat.card N) (f : X → Z)
    (hact : ∀ c ∈ longInvSwap K X a b, ∃ σ ∈ N, ∀ p ∈ holtDelta K X a b, f (c • p) = σ (f p))
    (hwd : ∀ p ∈ holtDelta K X a b, ∀ p' ∈ holtDelta K X a b, D.coord p = D.coord p' →
      f p = f p')
    (hsurj : ∀ z, ∃ p ∈ holtDelta K X a b, f p = z)
    (hreal : ∀ n ∈ N, orderOf n = 2 → ∃ c ∈ longInvSwap K X a b,
      ∀ p ∈ holtDelta K X a b, f (c • p) = n (f p)) :
    ∃ k₀ : D.ι,
      (∀ e : ∀ k, Perm (D.Ψc k),
        (∀ k, e k ∈ pairProducts (D.ρ k).range (D.coord a k) (D.coord b k)) → e k₀ = 1 →
          ∃ w ∈ Subgroup.closure (longInvSwap K X a b),
            (∀ p k, D.coord (w • p) k = e k (D.coord p k)) ∧
              ∀ p ∈ holtDelta K X a b, f (w • p) = f p) ∧
      (∀ x ∈ pairProducts (D.ρ k₀).range (D.coord a k₀) (D.coord b k₀),
        ∃ w ∈ Subgroup.closure (longInvSwap K X a b),
          (∀ p k, D.coord (w • p) k =
            (Pi.mulSingle k₀ x : ∀ k, Perm (D.Ψc k)) k (D.coord p k)) ∧
          ∃ σ : Perm Z, ∀ p ∈ holtDelta K X a b, f (w • p) = σ (f p)) ∧
      ¬ (∀ x ∈ pairProducts (D.ρ k₀).range (D.coord a k₀) (D.coord b k₀),
          ∀ y ∈ pairProducts (D.ρ k₀).range (D.coord a k₀) (D.coord b k₀), x * y = y * x) := by
  classical
  set Λ := holtDelta K X a b with hΛ
  set W := Subgroup.closure (longInvSwap K X a b) with hW
  have hWΛ : ∀ w ∈ W, ∀ p ∈ Λ, w • p ∈ Λ := by
    intro w hw p hp
    have hle : W ≤ stabilizer K Λ := (Subgroup.closure_le _).mpr fun c hc =>
      mem_stabilizer_holtDelta_of_mem_longInvSwap hc
    rw [← mem_stabilizer_iff.mp (hle hw)]
    exact Set.smul_mem_smul_set hp
  have hex : ∀ w ∈ W, ∃ σ ∈ N, ∀ p ∈ Λ, f (w • p) = σ (f p) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem c hc => exact hact c hc
    | one => exact ⟨1, one_mem _, fun p _ => by rw [one_smul, Perm.one_apply]⟩
    | mul w w' hw hw' ih ih' =>
      obtain ⟨σ, hσ, hσf⟩ := ih
      obtain ⟨σ', hσ', hσ'f⟩ := ih'
      exact ⟨σ * σ', mul_mem hσ hσ', fun p hp => by
        rw [mul_smul, hσf _ (hWΛ w' hw' p hp), hσ'f p hp, Perm.mul_apply]⟩
    | inv w hw ih =>
      obtain ⟨σ, hσ, hσf⟩ := ih
      refine ⟨σ⁻¹, inv_mem hσ, fun p hp => ?_⟩
      have h := hσf (w⁻¹ • p) (hWΛ _ (inv_mem hw) p hp)
      rw [smul_inv_smul] at h
      rw [h]
      exact (σ.symm_apply_apply _).symm
  have huniq : ∀ (w : K) (σ τ : Perm Z), (∀ p ∈ Λ, f (w • p) = σ (f p)) →
      (∀ p ∈ Λ, f (w • p) = τ (f p)) → σ = τ := fun w σ τ hσ hτ => Equiv.ext fun z => by
    obtain ⟨p, hp, rfl⟩ := hsurj z
    rw [← hσ p hp, hτ p hp]
  choose σ hσN hσ using fun w : W => hex w w.2
  let φ : W →* N :=
    { toFun := fun w => ⟨σ w, hσN w⟩
      map_one' := Subtype.ext (huniq 1 _ 1 (hσ 1) fun p _ => by
        rw [one_smul, Perm.one_apply])
      map_mul' := fun w w' => Subtype.ext (huniq ((w * w' : W) : K) _ _ (hσ _) fun p hp => by
        rw [Subgroup.coe_mul, mul_smul, hσ w _ (hWΛ _ w'.2 p hp), hσ w' p hp]
        rfl) }
  have hφ : ∀ (w : W), ∀ p ∈ Λ, f ((w : K) • p) = ((φ w : N) : Perm Z) (f p) :=
    fun w p hp => hσ w p hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n₀, hn₀⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hφsurj : Function.Surjective φ := by
    intro n
    have hn : n ∈ Subgroup.closure {y : N | orderOf y = 2} := by
      rw [closure_orderOf_eq_two_eq_top hn₀]
      exact Subgroup.mem_top n
    have hle : Subgroup.closure {y : N | orderOf y = 2} ≤ φ.range := by
      rw [Subgroup.closure_le]
      intro m hm
      obtain ⟨c, hc, hcf⟩ := hreal m m.2 (by rw [Subgroup.orderOf_coe]; exact hm)
      exact ⟨⟨c, Subgroup.subset_closure hc⟩,
        Subtype.ext (huniq c (σ ⟨c, Subgroup.subset_closure hc⟩) m
          (hσ ⟨c, Subgroup.subset_closure hc⟩) hcf)⟩
    exact hle hn
  have hWH : W ≤ jHull K X := Subgroup.closure_mono fun t ht => ht.1
  let τ : W →* (∀ k, Perm (D.Ψc k)) := (MonoidHom.pi D.ρ).comp (Subgroup.inclusion hWH)
  have hτ : ∀ (w : W) (p : X) (k : D.ι), D.coord ((w : K) • p) k = τ w k (D.coord p k) :=
    fun w p k => D.coord_smul ⟨w, hWH w.2⟩ p k
  have hker : τ.rangeRestrict.ker ≤ φ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    refine Subtype.ext (huniq w (σ w) 1 (hσ w) fun p hp => ?_)
    have hc : D.coord ((w : K) • p) = D.coord p := funext fun k => by
      rw [hτ, hw]
      rfl
    rw [Perm.one_apply]
    exact hwd _ (hWΛ _ w.2 p hp) p hp hc
  set φ' := (MonoidHom.liftOfSurjective τ.rangeRestrict τ.rangeRestrict_surjective) ⟨φ, hker⟩
    with hφ'def
  have hφ' : ∀ w : W, φ' (τ.rangeRestrict w) = φ w := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ w
  set Pk : ∀ k, Subgroup (Perm (D.Ψc k)) :=
    fun k => pairProducts (D.ρ k).range (D.coord a k) (D.coord b k) with hPk
  set P := Subgroup.pi Set.univ Pk with hPdef
  have hrange : τ.range = (Subgroup.closure ((↑) ⁻¹' longInvSwap K X a b :
      Set (jHull K X))).map (MonoidHom.pi D.ρ) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range,
      ← closure_preimage_eq_subgroupOf fun t ht => mem_jHull_of_mem_longInv ht.1]
  have hPQ : P ≤ τ.range := hrange ▸ D.pi_pairProducts_le_map_closure hne
  obtain ⟨s, hs⟩ := hne
  have hidx : P.relIndex τ.range ≤ 2 := by
    rw [hrange]
    exact D.relIndex_pi_pairProducts_le_two (s := ⟨s, mem_jHull_of_mem_longInv hs.1⟩) hs
  let ψ : P →* N := φ'.comp (Subgroup.inclusion hPQ)
  have hφ'surj : Function.Surjective φ' := fun n => by
    obtain ⟨w, rfl⟩ := hφsurj n
    exact ⟨_, hφ' w⟩
  have hψsurj : Function.Surjective ψ := by
    set I := (P.subgroupOf τ.range).map φ' with hI
    have hdvd : I.index ∣ P.relIndex τ.range := Subgroup.index_map_dvd _ hφ'surj
    have h0 : P.relIndex τ.range ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hItop : I = ⊤ := by
      have hpos : 0 < I.index := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero h0)
      have hle : I.index ≤ 2 := (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd).trans hidx
      interval_cases h : I.index
      · exact Subgroup.index_eq_one.mp h
      · have : I.Normal := Subgroup.normal_of_index_eq_two h
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal I with hb | ht
        · exfalso
          rw [hb, Subgroup.index_bot] at h
          have : Fact (Nat.card N).Prime := ⟨h ▸ Nat.prime_two⟩
          have : IsCyclic N := isCyclic_of_prime_card rfl
          obtain ⟨x, y, hxy⟩ := hN
          exact hxy (IsCyclic.commGroup.mul_comm x y)
        · exact ht
    intro n
    obtain ⟨q, hq, rfl⟩ : n ∈ I := hItop ▸ Subgroup.mem_top n
    exact ⟨⟨q, hq⟩, rfl⟩
  obtain ⟨k₀, hk₀1, hk₀2⟩ := exists_coord_of_surjective hN hψsurj
  have hlift : ∀ e : P, ∃ w : W, τ w = e ∧ φ w = ψ e := by
    intro e
    obtain ⟨w, hw⟩ := hPQ e.2
    refine ⟨w, hw, ?_⟩
    rw [← hφ' w]
    show φ' (τ.rangeRestrict w) = φ' (Subgroup.inclusion hPQ e)
    congr 1
    apply Subtype.ext
    rw [MonoidHom.coe_rangeRestrict]
    exact hw
  refine ⟨k₀, fun e he hek => ?_, fun x hx => ?_, fun hcomm => ?_⟩
  · obtain ⟨w, hτw, hφw⟩ := hlift ⟨e, (Subgroup.mem_pi _).mpr fun k _ => he k⟩
    have h1 : ψ ⟨e, (Subgroup.mem_pi _).mpr fun k _ => he k⟩ = 1 := hk₀1 _ hek
    refine ⟨w, w.2, fun p k => by rw [hτ, hτw], fun p hp => ?_⟩
    rw [hφ w p hp, hφw, h1]
    rfl
  · obtain ⟨w, hτw, -⟩ := hlift (piSingleHom Pk k₀ ⟨x, hx⟩)
    exact ⟨w, w.2, fun p k => by rw [hτ, hτw]; rfl, _, hφ w⟩
  · obtain ⟨n, n', hnn'⟩ := hN
    obtain ⟨x, rfl⟩ := hk₀2 n
    obtain ⟨x', rfl⟩ := hk₀2 n'
    apply hnn'
    have h : piSingleHom Pk k₀ x * piSingleHom Pk k₀ x' =
        piSingleHom Pk k₀ x' * piSingleHom Pk k₀ x := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm x x.2 x' x'.2)
    rw [← map_mul, h, map_mul]

omit [Finite K] in
theorem smul_mem_holtDelta_of_mem_closure {a b : X} {w : K}
    (hw : w ∈ Subgroup.closure (longInvSwap K X a b)) {p : X} (hp : p ∈ holtDelta K X a b) :
    w • p ∈ holtDelta K X a b := by
  have hle : Subgroup.closure (longInvSwap K X a b) ≤ stabilizer K (holtDelta K X a b) :=
    (Subgroup.closure_le _).mpr fun c hc => mem_stabilizer_holtDelta_of_mem_longInvSwap hc
  rw [← mem_stabilizer_iff.mp (hle hw)]
  exact Set.smul_mem_smul_set hp

theorem exists_coord_ne_of_fibre {a b : X} (hne : (longInvSwap K X a b).Nonempty)
    {Z : Type*} [Finite Z] [Nontrivial Z] {N : Subgroup (Perm Z)} [IsSimpleGroup N]
    (hN : ∃ x y : N, x * y ≠ y * x) (h2 : 2 ∣ Nat.card N) (f : X → Z)
    (hact : ∀ c ∈ longInvSwap K X a b, ∃ σ ∈ N, ∀ p ∈ holtDelta K X a b, f (c • p) = σ (f p))
    (hwd : ∀ p ∈ holtDelta K X a b, ∀ p' ∈ holtDelta K X a b, D.coord p = D.coord p' →
      f p = f p')
    (hsurj : ∀ z, ∃ p ∈ holtDelta K X a b, f p = z)
    (hreal : ∀ n ∈ N, orderOf n = 2 → ∃ c ∈ longInvSwap K X a b,
      ∀ p ∈ holtDelta K X a b, f (c • p) = n (f p)) :
    ∃ k₀ : D.ι, D.coord a k₀ ≠ D.coord b k₀ ∧ ∀ p ∈ holtDelta K X a b,
      ∀ p' ∈ holtDelta K X a b, f p = f p' → D.coord p k₀ = D.coord p' k₀ := by
  classical
  obtain ⟨k₀, hkill, hsingle, hnc⟩ := exists_coord_kill D hne hN h2 f hact hwd hsurj hreal
  set Λ := holtDelta K X a b with hΛ
  have hcX : ∀ p ∈ Λ, ∀ k, D.coord p k ∈
      holtDelta (D.ρ k).range (D.Ψc k) (D.coord a k) (D.coord b k) :=
    fun p hp k => D.coord_mem_holtDelta hp k
  have hdep : ∀ p ∈ Λ, ∀ p' ∈ Λ, D.coord p k₀ = D.coord p' k₀ → f p = f p' := by
    intro p hp p' hp' h
    have hex : ∀ k, ∃ e ∈ pairProducts (D.ρ k).range (D.coord a k) (D.coord b k),
        e (D.coord p k) = D.coord p' k := fun k =>
      exists_mem_pairProducts_apply_eq (hcX p hp k) (hcX p' hp' k)
    choose e he hep using hex
    set e' := Function.update e k₀ 1 with he'def
    have he' : ∀ k, e' k ∈ pairProducts (D.ρ k).range (D.coord a k) (D.coord b k) := by
      intro k
      rcases eq_or_ne k k₀ with rfl | hk
      · rw [he'def, Function.update_self]
        exact one_mem _
      · rw [he'def, Function.update_of_ne hk]
        exact he k
    have he'p : ∀ k, e' k (D.coord p k) = D.coord p' k := by
      intro k
      rcases eq_or_ne k k₀ with rfl | hk
      · rw [he'def, Function.update_self, Perm.one_apply, h]
      · rw [he'def, Function.update_of_ne hk, hep]
    obtain ⟨w, hw, hwc, hwf⟩ := hkill e' he' (by rw [he'def, Function.update_self])
    rw [← hwf p hp]
    exact hwd _ (smul_mem_holtDelta_of_mem_closure hw hp) p' hp' (funext fun k => by
      rw [hwc, he'p])
  have hnconst : ¬ ∀ p ∈ Λ, ∀ p' ∈ Λ, f p = f p' := by
    intro h
    obtain ⟨z, z', hzz'⟩ := exists_pair_ne Z
    obtain ⟨p, hp, rfl⟩ := hsurj z
    obtain ⟨p', hp', rfl⟩ := hsurj z'
    exact hzz' (h p hp p' hp')
  have hab : D.coord a k₀ ≠ D.coord b k₀ := by
    intro h
    refine hnconst fun p hp p' hp' => hdep p hp p' hp' ?_
    have h1 := hcX p hp k₀
    have h2 := hcX p' hp' k₀
    rw [h, D.holtDelta_range_rho_self, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  refine ⟨k₀, hab, fun p hp p' hp' hff => ?_⟩
  by_contra hne'
  rcases D.factor k₀ with ⟨hA, h7⟩ | hSE
  · apply hnconst
    suffices hall : ∀ q ∈ Λ, f q = f p from
      fun q hq q' hq' => (hall q hq).trans (hall q' hq').symm
    intro q hq
    set c := D.coord p k₀ with hcdef
    set c' := D.coord p' k₀ with hc'def
    set d := D.coord q k₀ with hddef
    by_cases hdc : d = c
    · exact hdep q hq p hp hdc
    have hAN : alternatingGroup (D.Ψc k₀) ≤ (D.ρ k₀).range := hA ▸ Subgroup.map_le_range _ _
    have hJ : longInv (Perm (D.Ψc k₀)) (D.Ψc k₀) ⊆ (D.ρ k₀).range :=
      longInv_perm_subset_of_alternatingGroup_le hAN ⟨D.tHull, rfl⟩
        (D.rho_mem_longInv D.t_mem k₀)
    have hcompl := D.holtDelta_range_rho_eq_compl hA hab
    have hmem : ∀ r ∈ Λ, D.coord r k₀ ≠ D.coord a k₀ ∧ D.coord r k₀ ≠ D.coord b k₀ := by
      intro r hr
      have h := hcX r hr k₀
      rw [hcompl, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact h
    obtain ⟨e, heP, hec, hec'⟩ : ∃ e ∈ pairProducts (D.ρ k₀).range (D.coord a k₀)
        (D.coord b k₀), e c = c ∧ e c' = d := by
      by_cases hdc' : d = c'
      · exact ⟨1, one_mem _, rfl, hdc'.symm⟩
      obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({D.coord a k₀, D.coord b k₀, c, c', d} : Finset (D.Ψc k₀)))
        (t := Finset.univ) (Finset.card_le_five.trans_lt (by rw [Finset.card_univ]; omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      obtain ⟨hxa, hxb, hxc, hxc', hxd⟩ := hx
      obtain ⟨hca, hcb⟩ := hmem p hp
      obtain ⟨hc'a, hc'b⟩ := hmem p' hp'
      obtain ⟨hda, hdb⟩ := hmem q hq
      have hfix : ∀ y, y ≠ c' → y ≠ x → y ≠ d → (swap c' x * swap c' d) y = y :=
        fun y h1 h2 h3 => by
          rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
      refine ⟨swap c' x * swap c' d, alternatingGroup_inf_stabilizer_le_pairProducts hJ
        (D.odd_card_Ψc k₀) hab ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · exact (Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hxc') (fun h => hdc' h.symm)
          hxd).mem_alternatingGroup
      · exact hfix _ (Ne.symm hc'a) (Ne.symm hxa) (Ne.symm hda)
      · exact hfix _ (Ne.symm hc'b) (Ne.symm hxb) (Ne.symm hdb)
      · exact hfix _ hne' (Ne.symm hxc) (Ne.symm hdc)
      · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hdc' (Ne.symm hxd)]
    obtain ⟨w, hw, hwc, σ, hσ⟩ := hsingle e heP
    have hwp : f (w • p) = f p := hdep _ (smul_mem_holtDelta_of_mem_closure hw hp) p hp (by
      rw [hwc, Pi.mulSingle_eq_same, hec])
    have hwp' : f (w • p') = f q := hdep _ (smul_mem_holtDelta_of_mem_closure hw hp') q hq (by
      rw [hwc, Pi.mulSingle_eq_same, hec'])
    rw [← hwp', hσ p' hp', ← hff, ← hσ p hp, hwp]
  · apply hnc
    intro x hx y hy
    have hR := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
    obtain ⟨n, i, e, hBA⟩ := hSE.exists_isBenderAction
    have : IsCyclic ↥(stabilizer (D.M k₀) (D.coord a k₀) ⊓
        stabilizer (D.M k₀) (D.coord b k₀)) := hBA.isCyclic_stabilizer_inf hab
    have hle := pairProducts_le (D.ρ k₀).range (D.coord a k₀) (D.coord b k₀)
    have hx' := hle hx
    have hy' := hle hy
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hx' hy'
    obtain ⟨⟨hxN, hxa⟩, hxb⟩ := hx'
    obtain ⟨⟨hyN, hya⟩, hyb⟩ := hy'
    have hxS : (⟨x, hR ▸ hxN⟩ : D.M k₀) ∈ stabilizer (D.M k₀) (D.coord a k₀) ⊓
        stabilizer (D.M k₀) (D.coord b k₀) := ⟨hxa, hxb⟩
    have hyS : (⟨y, hR ▸ hyN⟩ : D.M k₀) ∈ stabilizer (D.M k₀) (D.coord a k₀) ⊓
        stabilizer (D.M k₀) (D.coord b k₀) := ⟨hya, hyb⟩
    have h := (inferInstance : IsMulCommutative ↥(stabilizer (D.M k₀) (D.coord a k₀) ⊓
        stabilizer (D.M k₀) (D.coord b k₀))).is_comm.comm ⟨_, hxS⟩ ⟨_, hyS⟩
    exact congrArg (fun z : ↥(stabilizer (D.M k₀) (D.coord a k₀) ⊓
        stabilizer (D.M k₀) (D.coord b k₀)) => ((z : D.M k₀) : Perm (D.Ψc k₀))) h

end Coordinate

section Realization

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

theorem exists_mem_centralizer_fix_rho_eq (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i : D.ι}
    (hi : IsNaturalSE (D.M i)) (γ : holtDelta G Ω α β) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (hℓV : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ i → D.coord δ j = D.coord γ j) →
      (δ : Ω) ∈ fixSet Ω V)
    {x : Perm (D.Ψc i)} (hxM : x ∈ D.M i) (hx : orderOf x = 2)
    (hxγ : x (D.coord γ i) = D.coord γ i) :
    ∃ (c : G) (hc : c ∈ longInvSwap G Ω α β), c ∈ Subgroup.centralizer (V : Set G) ∧
      c • (γ : Ω) = γ ∧
      D.ρ i ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β
        (Subgroup.subset_closure hc)), twoPointElt_mem_jHull hS.star
          (Subgroup.subset_closure hc)⟩ = x := by
  classical
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D
  have hxJ : x ∈ longInv (Perm (D.Ψc i)) (D.Ψc i) := by
    refine ⟨hx, ?_⟩
    have := hi.existsUnique_fixed (x := ⟨x, hxM⟩) (by rwa [Subgroup.orderOf_mk])
    simpa using this
  obtain ⟨w, hw, hwγ⟩ := γ.2
  set wΔ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hw)),
      twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hw)⟩
  have hwΔJ : (wΔ : twoPointSection G Ω α β) ∈
      longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mpr ⟨w, hw, fun δ => rfl⟩
  have hwfix : ∀ j, D.ρ j wΔ (D.coord γ j) = D.coord γ j := fun j => by
    rw [← D.coord_smul]
    congr 1
    exact Subtype.ext hwγ
  set y : ∀ j, Perm (D.Ψc j) := Function.update (fun j => D.ρ j wΔ) i x with hy
  have hyr : ∀ j, y j ∈ (D.ρ j).range := by
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [hy, Function.update_self]
      exact Subgroup.map_le_range _ _ hxM
    · rw [hy, Function.update_of_ne hj]
      exact ⟨wΔ, rfl⟩
  have hyJ : ∀ j, y j ∈ longInvAt (Perm (D.Ψc j)) (D.Ψc j) (D.coord γ j) := by
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [hy, Function.update_self]
      exact ⟨hxJ, hxγ⟩
    · rw [hy, Function.update_of_ne hj]
      exact ⟨D.rho_mem_longInv hwΔJ j, hwfix j⟩
  obtain ⟨u, huJ, hu⟩ := D.exists_mem_longInvAt_rho_eq γ y hyr hyJ
  obtain ⟨c₀, hc₀, hc₀γ, hc₀u⟩ := (hS.mem_longInvAt_twoPointSection_iff hαβ h3Δ _).mp huJ
  set ℓ : Set Ω := Subtype.val '' {δ : holtDelta G Ω α β |
    ∀ j, j ≠ i → D.coord δ j = D.coord γ j} with hℓ
  have hline : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ i → D.coord δ j = D.coord γ j) →
      ∀ j, j ≠ i → D.coord ((u : twoPointSection G Ω α β) • δ) j = D.coord γ j := by
    intro δ hδ j hj
    rw [D.coord_smul, hu j, hy, Function.update_of_ne hj, hδ j hj, hwfix j]
  have hc₀mem : ∀ ω ∈ ℓ, c₀ • ω ∈ ℓ := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact ⟨(u : twoPointSection G Ω α β) • δ, hline δ hδ, hc₀u δ⟩
  have hc₀ℓ : c₀ ∈ stabilizer G ℓ := by
    rw [mem_stabilizer_set]
    intro ω
    refine ⟨fun h => ?_, hc₀mem ω⟩
    have := hc₀mem _ h
    rwa [smul_smul, mul_self_eq_one_of_mem_longInv hc₀.1, one_smul] at this
  have hℓV' : ℓ ⊆ fixSet Ω V := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact hℓV δ hδ
  obtain ⟨c, hc, hcV, hcℓ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hV hVαβ
    (⟨(γ : Ω), γ, fun j _ => rfl, rfl⟩ : ℓ.Nonempty) hℓV' hc₀ hc₀ℓ
  refine ⟨c, hc, hcV, ?_, Equiv.ext fun ψ => ?_⟩
  · rw [hcℓ γ ⟨γ, fun j _ => rfl, rfl⟩, hc₀γ]
  obtain ⟨δ, hδ⟩ := D.exists_coord_eq_update γ i ψ
  have hδℓ : ∀ j, j ≠ i → D.coord δ j = D.coord γ j := fun j hj => by
    rw [hδ, Function.update_of_ne hj]
  have hψ : D.coord δ i = ψ := by rw [hδ, Function.update_self]
  have hx' : x = y i := by rw [hy, Function.update_self]
  rw [hx', ← hu i, ← hψ, ← D.coord_smul, ← D.coord_smul]
  congr 1
  apply Subtype.ext
  exact (hcℓ δ ⟨δ, hδℓ, rfl⟩).trans (hc₀u δ).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem coe_mul_pow_smul_centralizerImageElt {V : Subgroup G} {c c' : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (hc' : c' ∈ Subgroup.centralizer (V : Set G))
    (m : ℕ) (ω : fixSet Ω V) :
    (((centralizerImageElt (Ω := Ω) hc' * centralizerImageElt (Ω := Ω) hc) ^ m • ω :
      fixSet Ω V) : Ω) = (c' * c) ^ m • (ω : Ω) := by
  induction m generalizing ω with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ m ih =>
    rw [pow_succ, pow_succ, mul_smul, mul_smul, ih, mul_smul, mul_smul]
    rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem coe_mul_pow_smul_twoPointElt {α β : Ω} {c c' : G}
    (hc : c ∈ stabilizer G ({α, β} : Set Ω)) (hc' : c' ∈ stabilizer G ({α, β} : Set Ω))
    (m : ℕ) (δ : holtDelta G Ω α β) :
    (((twoPointElt hc' * twoPointElt hc) ^ m • δ : holtDelta G Ω α β) : Ω) =
      (c' * c) ^ m • (δ : Ω) := by
  induction m generalizing δ with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ m ih =>
    rw [pow_succ, pow_succ, mul_smul, mul_smul, ih, mul_smul, mul_smul]
    rfl

variable [FaithfulSMul G Ω]

theorem coord_eq_of_mem_orbit (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {l : D'.ι}
    (hl : IsNaturalSE (D'.M l)) {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUαβ : U ≤ stabilizer G α ⊓ stabilizer G β)
    (hline : ∀ δ δ' : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω U →
      (∀ j, j ≠ l → D'.coord δ' j = D'.coord δ j) → (δ' : Ω) ∈ fixSet Ω U)
    (h3 : 3 ≤ Nat.card (fixSet Ω U)) {p p' : fixSet Ω U} (hp : (p : Ω) ∈ holtDelta G Ω α β)
    (hp' : (p' : Ω) ∈ holtDelta G Ω α β)
    (horb : p' ∈ orbit (jOddCore (centralizerImage Ω U) (fixSet Ω U)) p) :
    D'.coord ⟨p, hp⟩ l = D'.coord ⟨p', hp'⟩ l := by
  classical
  by_contra hne
  set z := D'.coord ⟨p, hp⟩ l with hz
  set z' := D'.coord ⟨p', hp'⟩ l with hz'
  obtain ⟨n, e, f, hA⟩ := IsNaturalSE.exists_isBenderAction hl
  have hcard : 3 ≤ (longInvAt (D'.M l) (D'.Ψc l) z).ncard := by
    rw [hA.ncard_longInvAt]
    have := hA.four_le_q
    omega
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero
    (s := longInvAt (D'.M l) (D'.Ψc l) z) (by omega)
  obtain ⟨y', hy', hyy'⟩ := Set.exists_ne_of_one_lt_ncard
    (s := longInvAt (D'.M l) (D'.Ψc l) z) (by omega) y
  set Y : Perm (D'.Ψc l) := (y : Perm (D'.Ψc l)) with hYdef
  set Y' : Perm (D'.Ψc l) := (y' : Perm (D'.Ψc l)) with hY'def
  have hYJ : Y ∈ longInv (Perm (D'.Ψc l)) (D'.Ψc l) := mem_longInv_subgroup_iff.mp hy.1
  have hY'J : Y' ∈ longInv (Perm (D'.Ψc l)) (D'.Ψc l) := mem_longInv_subgroup_iff.mp hy'.1
  have hYY : Y * Y = 1 := mul_self_eq_one_of_mem_longInv hYJ
  have hY'Y' : Y' * Y' = 1 := mul_self_eq_one_of_mem_longInv hY'J
  have hYY' : Y * Y' = Y' * Y := hl.commute_of_mem_mulLongInvClosure
    (hl.mem_mulLongInvClosure_of_mul_self y.2 hy.2 hYY)
    (hl.mem_mulLongInvClosure_of_mul_self y'.2 hy'.2 hY'Y')
  have hP2 : (Y' * Y) * (Y' * Y) = 1 := by
    rw [← hYY', mul_assoc, ← mul_assoc Y', ← hYY', mul_assoc, hY'Y', mul_one, hYY]
  have hP1 : Y' * Y ≠ 1 := fun h => hyy' (Subtype.ext (by
    show Y' = Y
    rw [← inv_eq_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hYY]))
  have hmove : (Y' * Y) z' ≠ z' := by
    intro h
    obtain ⟨w₀, -, huniq⟩ := hl.existsUnique_fixed (x := ⟨Y' * Y, mul_mem y'.2 y.2⟩)
      (orderOf_eq_prime (by rw [sq]; exact Subtype.ext hP2) fun h1 =>
        hP1 (congrArg Subtype.val h1))
    have hYz : Y z = z := hy.2
    have hY'z : Y' z = z := hy'.2
    have hz0 : (Y' * Y) z = z := by rw [Perm.mul_apply, hYz, hY'z]
    exact hne ((huniq z hz0).trans (huniq z' h).symm)
  have hℓp : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ l → D'.coord δ j = D'.coord ⟨p, hp⟩ j) →
      (δ : Ω) ∈ fixSet Ω U := fun δ hδ => hline ⟨p, hp⟩ δ p.2 hδ
  obtain ⟨c, hc, hcU, hcp, hcY⟩ := exists_mem_centralizer_fix_rho_eq hS hαβ D' hl ⟨p, hp⟩ hU
    hUαβ hℓp y.2 hYJ.1 hy.2
  obtain ⟨c', hc', hc'U, hc'p, hc'Y⟩ := exists_mem_centralizer_fix_rho_eq hS hαβ D' hl ⟨p, hp⟩
    hU hUαβ hℓp y'.2 hY'J.1 hy'.2
  have hcF : centralizerImageElt (Ω := Ω) hcU ∈
      longInvAt (centralizerImage Ω U) (fixSet Ω U) p :=
    (hS.mem_longInvAt_centralizerImage_iff hU h3 _).mpr ⟨c, ⟨hc.1, hcp⟩, hcU, fun ω => rfl⟩
  have hc'F : centralizerImageElt (Ω := Ω) hc'U ∈
      longInvAt (centralizerImage Ω U) (fixSet Ω U) p :=
    (hS.mem_longInvAt_centralizerImage_iff hU h3 _).mpr ⟨c', ⟨hc'.1, hc'p⟩, hc'U, fun ω => rfl⟩
  obtain ⟨m, hm, hmB⟩ := exists_odd_pow_smul_eq_of_mem_longInvAt
    (hS.star_centralizerImage hU h3) hcF hc'F
  have hfix : (c' * c) ^ m • (p' : Ω) = p' := by
    rw [← coe_mul_pow_smul_centralizerImageElt hcU hc'U m p', hmB p' horb]
  have hcX := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)
  have hc'X := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc')
  have hcH := twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hc)
  have hc'H := twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hc')
  have hpt : ((((⟨twoPointElt hc'X, hc'H⟩ * ⟨twoPointElt hcX, hcH⟩ :
      jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) ^ m :
        jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) : twoPointSection G Ω α β) •
      (⟨p', hp'⟩ : holtDelta G Ω α β)) = ⟨p', hp'⟩ :=
    Subtype.ext ((coe_mul_pow_smul_twoPointElt hcX hc'X m ⟨p', hp'⟩).trans hfix)
  have h1 := D'.coord_smul ((⟨twoPointElt hc'X, hc'H⟩ * ⟨twoPointElt hcX, hcH⟩ :
    jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) ^ m) ⟨p', hp'⟩ l
  rw [hpt, map_pow, map_mul, hcY, hc'Y] at h1
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hP2, one_pow, one_mul] at h1
  exact hmove h1.symm

theorem exists_coord_ne (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {l : D'.ι}
    (hl : IsNaturalSE (D'.M l)) {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUαβ : U ≤ stabilizer G α ⊓ stabilizer G β)
    (hline : ∀ δ δ' : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω U →
      (∀ j, j ≠ l → D'.coord δ' j = D'.coord δ j) → (δ' : Ω) ∈ fixSet Ω U)
    (γ₀ : holtDelta G Ω α β) (hγ₀ : (γ₀ : Ω) ∈ fixSet Ω U) (hα : α ∈ fixSet Ω U)
    (hβ : β ∈ fixSet Ω U) (DU : HoltData (centralizerImage Ω U) (fixSet Ω U)) :
    ∃ k₀ : DU.ι, DU.coord ⟨α, hα⟩ k₀ ≠ DU.coord ⟨β, hβ⟩ k₀ ∧
      ∀ (δ δ' : holtDelta G Ω α β) (hδ : (δ : Ω) ∈ fixSet Ω U)
        (hδ' : (δ' : Ω) ∈ fixSet Ω U), D'.coord δ l = D'.coord δ' l →
          DU.coord ⟨δ, hδ⟩ k₀ = DU.coord ⟨δ', hδ'⟩ k₀ := by
  classical
  have hab : (⟨α, hα⟩ : fixSet Ω U) ≠ ⟨β, hβ⟩ := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hU hab
  have hΛ := hS.holtDelta_centralizerImage hU h3 hab
  have hmemΛ : ∀ p : fixSet Ω U, p ∈ holtDelta (centralizerImage Ω U) (fixSet Ω U)
      ⟨α, hα⟩ ⟨β, hβ⟩ ↔ (p : Ω) ∈ holtDelta G Ω α β := fun p => by
    rw [hΛ, Set.mem_preimage]
  set f : fixSet Ω U → D'.Ψc l := fun p =>
    if h : (p : Ω) ∈ holtDelta G Ω α β then D'.coord ⟨p, h⟩ l else D'.coord γ₀ l with hfdef
  have hf : ∀ (p : fixSet Ω U) (h : (p : Ω) ∈ holtDelta G Ω α β), f p = D'.coord ⟨p, h⟩ l :=
    fun p h => dite_eq_left h
  have hgen : ∀ (π : centralizerImage Ω U) (c : G) (hc : c ∈ longInvSwap G Ω α β),
      (∀ ω : fixSet Ω U, ((π : Perm (fixSet Ω U)) ω : Ω) = c • (ω : Ω)) →
        ∀ p : fixSet Ω U, (p : Ω) ∈ holtDelta G Ω α β →
          f (π • p) = D'.ρ l ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β
            (Subgroup.subset_closure hc)), twoPointElt_mem_jHull hS.star
              (Subgroup.subset_closure hc)⟩ (f p) := by
    intro π c hc hcπ p hp
    have hp' : ((π • p : fixSet Ω U) : Ω) ∈ holtDelta G Ω α β := by
      rw [show ((π • p : fixSet Ω U) : Ω) = c • (p : Ω) from hcπ p]
      exact (mem_stabilizer_set.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hc) _).mpr hp
    rw [hf _ hp', hf _ hp, ← D'.coord_smul]
    congr 1
    exact Subtype.ext (hcπ p)
  have hsurj : ∀ z, ∃ p ∈ holtDelta (centralizerImage Ω U) (fixSet Ω U) ⟨α, hα⟩ ⟨β, hβ⟩,
      f p = z := by
    intro z
    obtain ⟨δ, hδ⟩ := D'.exists_coord_eq_update γ₀ l z
    have hδU := hline γ₀ δ hγ₀ fun j hj => by rw [hδ, Function.update_of_ne hj]
    refine ⟨⟨δ, hδU⟩, (hmemΛ _).mpr δ.2, ?_⟩
    rw [hf _ δ.2]
    show D'.coord δ l = z
    rw [hδ, Function.update_self]
  have : IsSimpleGroup (D'.M l) := D'.isSimpleGroup_M l
  have hN : ∃ x y : D'.M l, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact D'.not_isMulCommutative_M l (isMulCommutative_iff.mpr h)
  have : Nontrivial (D'.Ψc l) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := D'.five_le_card l; omega)
  obtain ⟨u, hu, huU⟩ := hS.exists_mem_longInvSwap_centralizer hαβ hU hUαβ
  have hne : (longInvSwap (centralizerImage Ω U) (fixSet Ω U) ⟨α, hα⟩ ⟨β, hβ⟩).Nonempty :=
    ⟨centralizerImageElt huU,
      (hS.mem_longInvSwap_centralizerImage_iff hU h3 _).mpr ⟨u, hu, huU, fun ω => rfl⟩⟩
  obtain ⟨k₀, hk₀, hk₀f⟩ := exists_coord_ne_of_fibre DU hne hN (D'.factor l).two_dvd_card f
    (fun π hπ => by
      obtain ⟨c, hc, -, hcπ⟩ := (hS.mem_longInvSwap_centralizerImage_iff hU h3 π).mp hπ
      exact ⟨_, rho_twoPointElt_mem_M_of_isNaturalSE hS.star D' hl (Subgroup.subset_closure hc),
        fun p hp => hgen π c hc hcπ p ((hmemΛ p).mp hp)⟩)
    (fun p hp p' hp' hpp' => by
      rw [hf _ ((hmemΛ p).mp hp), hf _ ((hmemΛ p').mp hp')]
      exact coord_eq_of_mem_orbit hS hαβ D' hl hU hUαβ hline h3 _ _
        ((DU.coord_eq_iff p p').mp hpp'))
    hsurj
    (fun n hn hn2 => by
      obtain ⟨z, hz, -⟩ := hl.existsUnique_fixed (x := ⟨n, hn⟩) (by rwa [Subgroup.orderOf_mk])
      obtain ⟨p, hp, hpz⟩ := hsurj z
      have hpΔ := (hmemΛ p).mp hp
      have hℓ : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ l → D'.coord δ j = D'.coord ⟨p, hpΔ⟩ j) →
          (δ : Ω) ∈ fixSet Ω U := fun δ hδ => hline ⟨p, hpΔ⟩ δ p.2 hδ
      obtain ⟨c, hc, hcU, -, hcn⟩ := exists_mem_centralizer_fix_rho_eq hS hαβ D' hl ⟨p, hpΔ⟩
        hU hUαβ hℓ hn hn2 (by rw [← hf _ hpΔ, hpz]; exact hz)
      refine ⟨centralizerImageElt hcU, (hS.mem_longInvSwap_centralizerImage_iff hU h3 _).mpr
        ⟨c, hc, hcU, fun ω => rfl⟩, fun p' hp' => ?_⟩
      rw [hgen _ c hc (fun ω => rfl) p' ((hmemΛ p').mp hp'), hcn])
  refine ⟨k₀, hk₀, fun δ δ' hδ hδ' hll => hk₀f _ ((hmemΛ _).mpr δ.2) _ ((hmemΛ _).mpr δ'.2) ?_⟩
  rw [hf _ δ.2, hf _ δ'.2]
  exact hll

theorem false_of_mem_closure_smul_eq (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {l : D'.ι}
    (hl : IsNaturalSE (D'.M l)) {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hUαβ : U ≤ stabilizer G α ⊓ stabilizer G β)
    (hline : ∀ δ δ' : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω U →
      (∀ j, j ≠ l → D'.coord δ' j = D'.coord δ j) → (δ' : Ω) ∈ fixSet Ω U)
    {g : G} (hg : g ∈ Subgroup.closure (longInv G Ω ∩ Subgroup.centralizer (U : Set G)))
    (δ δ' : holtDelta G Ω α β) (hδ : (δ : Ω) ∈ fixSet Ω U) (hδ' : (δ' : Ω) ∈ fixSet Ω U)
    (hgα : g • α = δ) (hgβ : g • β = δ') (hll : D'.coord δ l = D'.coord δ' l) : False := by
  have hα : α ∈ fixSet Ω U := mem_fixSet_iff_le_stabilizer.mpr (hUαβ.trans inf_le_left)
  have hβ : β ∈ fixSet Ω U := mem_fixSet_iff_le_stabilizer.mpr (hUαβ.trans inf_le_right)
  have hab : (⟨α, hα⟩ : fixSet Ω U) ≠ ⟨β, hβ⟩ := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hU hab
  obtain ⟨DU⟩ := hS.holtData_centralizerImage hU hU1 h3
  obtain ⟨k₀, hk₀, hk₀B⟩ := exists_coord_ne hS hαβ D' hl hU hUαβ hline δ hδ hα hβ DU
  have hSC : longInv G Ω ∩ Subgroup.centralizer (U : Set G) ⊆
      Subgroup.centralizer (U : Set G) := Set.inter_subset_right
  have hgC : g ∈ Subgroup.centralizer (U : Set G) := (Subgroup.closure_le _).mpr hSC hg
  let ψU : Subgroup.centralizer (U : Set G) →* centralizerImage Ω U :=
    (MulAction.toPermHom (Subgroup.centralizer (U : Set G)) (fixSet Ω U)).rangeRestrict
  have hmem : (⟨g, hgC⟩ : Subgroup.centralizer (U : Set G)) ∈ Subgroup.closure ((↑) ⁻¹'
      (longInv G Ω ∩ Subgroup.centralizer (U : Set G)) :
        Set (Subgroup.centralizer (U : Set G))) := by
    rw [closure_preimage_eq_subgroupOf hSC]
    exact hg
  have hle : (Subgroup.closure ((↑) ⁻¹' (longInv G Ω ∩ Subgroup.centralizer (U : Set G)) :
      Set (Subgroup.centralizer (U : Set G)))).map ψU ≤
        jHull (centralizerImage Ω U) (fixSet Ω U) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_jHull_of_mem_longInv ((hS.mem_longInv_centralizerImage_iff hU h3 _).mpr
      ⟨x, hx.1, x.2, fun ω => rfl⟩)
  have hgH : centralizerImageElt (Ω := Ω) hgC ∈ jHull (centralizerImage Ω U) (fixSet Ω U) :=
    hle ⟨_, hmem, rfl⟩
  have h1 := DU.coord_smul ⟨_, hgH⟩ ⟨α, hα⟩ k₀
  have h2 := DU.coord_smul ⟨_, hgH⟩ ⟨β, hβ⟩ k₀
  have e1 : ((⟨_, hgH⟩ : jHull (centralizerImage Ω U) (fixSet Ω U)) :
      centralizerImage Ω U) • (⟨α, hα⟩ : fixSet Ω U) = ⟨δ, hδ⟩ := Subtype.ext hgα
  have e2 : ((⟨_, hgH⟩ : jHull (centralizerImage Ω U) (fixSet Ω U)) :
      centralizerImage Ω U) • (⟨β, hβ⟩ : fixSet Ω U) = ⟨δ', hδ'⟩ := Subtype.ext hgβ
  rw [e1] at h1
  rw [e2] at h2
  exact hk₀ ((DU.ρ k₀ ⟨_, hgH⟩).injective (h1.symm.trans ((hk₀B δ δ' hδ hδ' hll).trans h2)))

end Realization

end P49S7

end CFSG.Holt.H78
