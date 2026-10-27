module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Co2Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem Level55.conj_t_of_mem_normPair (d : Level55 G t z) {n : G} (hnz : n * z = z * n)
    (hn : n ∈ normPair z t) : n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * z := by
  have hnt : n * t * n⁻¹ ∈ pair z t := (mem_normalizer_iff.1 hn t).1 (t_mem_pair z t)
  rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hnt with h | h | h | h
  · exfalso
    have ht1 : t = 1 := by simpa using h
    have : orderOf t = 1 := by rw [ht1, orderOf_one]
    have := d.t_ord
    omega
  · exfalso
    apply d.z_ne_t
    calc z = n⁻¹ * z * n := by rw [mul_assoc, ← hnz, inv_mul_cancel_left]
      _ = n⁻¹ * (n * t * n⁻¹) * n := by rw [h]
      _ = t := by group
  · exact Or.inl h
  · exact Or.inr (h.trans d.zt_comm)

theorem mem_centPair_of_conj_t {n : G} (hnz : n * z = z * n) (h : n * t * n⁻¹ = t) :
    n ∈ centPair z t := by
  refine mem_centPair_iff.2 ⟨hnz.symm, ?_⟩
  calc t * n = (n * t * n⁻¹) * n := by rw [h]
    _ = n * t := by group

theorem conj_mem_centPair_of_mem_normPair {n k : G} (hn : n ∈ normPair z t)
    (hk : k ∈ centPair z t) : n * k * n⁻¹ ∈ centPair z t := by
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : n⁻¹ * a * n ∈ pair z t := by
    have := (mem_normalizer_iff.1 (inv_mem hn) a).1 ha
    simpa using this
  have hcomm : (n⁻¹ * a * n) * k = k * (n⁻¹ * a * n) := mem_centralizer_iff.1 hk _ ha'
  calc a * (n * k * n⁻¹) = n * ((n⁻¹ * a * n) * k) * n⁻¹ := by group
    _ = n * (k * (n⁻¹ * a * n)) * n⁻¹ := by rw [hcomm]
    _ = (n * k * n⁻¹) * a := by group

theorem conj_mem_O2In_of_conj_mem {K : Subgroup G} {n : G} (hn : ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    (hn' : ∀ k ∈ K, n⁻¹ * k * n ∈ K) : ∀ y ∈ O2In K, n * y * n⁻¹ ∈ O2In K := by
  intro y hy
  set Y' : Subgroup G := (O2In K).map (MulAut.conj n).toMonoidHom with hY'
  have hY'K : Y' ≤ K := by
    rintro _ ⟨y', hy', rfl⟩
    exact hn y' (O2In_le _ hy')
  have hnorm : (Y'.subgroupOf K).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [mem_subgroupOf] at hm ⊢
    obtain ⟨y', hy', hyn⟩ := hm
    have hg : n⁻¹ * (g : G) * n ∈ K := hn' g g.2
    refine ⟨(n⁻¹ * (g : G) * n) * y' * (n⁻¹ * (g : G) * n)⁻¹, ?_, ?_⟩
    · exact (normal_subgroupOf_O2In K).conj_mem ⟨y', O2In_le _ hy'⟩ (mem_subgroupOf.2 hy')
        ⟨_, hg⟩
    · have : (MulAut.conj n) y' = (m : G) := hyn
      rw [MulAut.conj_apply] at this
      show n * ((n⁻¹ * (g : G) * n) * y' * (n⁻¹ * (g : G) * n)⁻¹) * n⁻¹ =
        (g : G) * (m : G) * (g : G)⁻¹
      rw [← this]
      group
  have hp : IsPGroup 2 Y' := (isPGroup_O2In K).of_equiv
    (Subgroup.equivMapOfInjective _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective)
  exact le_O2In hY'K hnorm hp ⟨y, hy, rfl⟩

theorem conj_mem_O2In_centPair_of_mem_normPair {n y : G} (hn : n ∈ normPair z t)
    (hy : y ∈ O2In (centPair z t)) : n * y * n⁻¹ ∈ O2In (centPair z t) :=
  conj_mem_O2In_of_conj_mem (fun k hk => conj_mem_centPair_of_mem_normPair hn hk)
    (fun k hk => by simpa using conj_mem_centPair_of_mem_normPair (inv_mem hn) hk) y hy

theorem Level55.mem_centPair_or_mul_mem (d : Level55 G t z) {x n : G} (hxz : x * z = z * x)
    (hxt : x * t * x⁻¹ = t * z) (hnz : n * z = z * n) (hn : n ∈ normPair z t) :
    n ∈ centPair z t ∨ n * x ∈ centPair z t := by
  have hzz := d.z_mul_self
  rcases d.conj_t_of_mem_normPair hnz hn with h | h
  · exact Or.inl (mem_centPair_of_conj_t hnz h)
  · right
    refine mem_centPair_of_conj_t (by rw [mul_assoc, hxz, ← mul_assoc, hnz, mul_assoc]) ?_
    have hnz' : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
    calc n * x * t * (n * x)⁻¹ = n * (x * t * x⁻¹) * n⁻¹ := by group
      _ = n * (t * z) * n⁻¹ := by rw [hxt]
      _ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
      _ = (t * z) * z := by rw [h, hnz']
      _ = t := by rw [mul_assoc, hzz, mul_one]

theorem Level55.relIndex_centPair_eq_two (d : Level55 G t z) {N : Subgroup G}
    (hNC : N ≤ centZ z) (hNn : N ≤ normPair z t) {x : G} (hxN : x ∈ N)
    (hxK : x ∉ centPair z t) : (centPair z t).relIndex N = 2 := by
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 (hNC hxN)
  have hxt : x * t * x⁻¹ = t * z := (d.conj_t_of_mem_normPair hxz (hNn hxN)).resolve_left
    (fun h => hxK (mem_centPair_of_conj_t hxz h))
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hxN⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, Subgroup.coe_mul]
  have hb := b.2
  have hbz : (b : G) * z = z * b := mem_centralizer_singleton_iff.1 (hNC hb)
  rcases d.mem_centPair_or_mul_mem hxz hxt hbz (hNn hb) with h | h
  · exact Or.inr ⟨h, fun hbx => hxK (by simpa using mul_mem (inv_mem h) hbx)⟩
  · exact Or.inl ⟨h, fun hb' => hxK (by simpa using mul_mem (inv_mem hb') h)⟩

structure Level55.Good (_d : Level55 G t z) (N Y₀ : Subgroup G) : Prop where
  le : Y₀ ≤ N
  normal : ∀ n ∈ N, ∀ u ∈ Y₀, n * u * n⁻¹ ∈ Y₀
  pgroup : IsPGroup 2 Y₀
  O2K_le : O2In (centPair z t) ≤ Y₀
  inf_le : centPair z t ⊓ Y₀ ≤ O2In (centPair z t)
  decomp : ∀ n ∈ N, ∃ k ∈ centPair z t, ∃ w ∈ Y₀, n = k * w
  comm : ∀ a ∈ Y₀, ∀ b ∈ Y₀, a * b * a⁻¹ * b⁻¹ ∈ zpowers z
  cent : ∀ n ∈ N, (∀ w ∈ Y₀, n * w * n⁻¹ * w⁻¹ ∈ zpowers z) → n ∈ Y₀

theorem Level55.Good.nonempty_quotient {d : Level55 G t z} {N Y₀ : Subgroup G}
    (hg : d.Good N Y₀) (hKN : centPair z t ≤ N) [(Y₀.subgroupOf N).Normal] :
    Nonempty (↥N ⧸ Y₀.subgroupOf N ≃* Carrier .Co2) := by
  obtain ⟨e⟩ := d.quot
  let φ : ↥(centPair z t) →* ↥N ⧸ Y₀.subgroupOf N :=
    (QuotientGroup.mk' (Y₀.subgroupOf N)).comp (Subgroup.inclusion hKN)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, w, hw, hnkw⟩ := hg.decomp n n.2
    refine ⟨⟨k, hk⟩, ?_⟩
    show (QuotientGroup.mk (⟨k, hKN hk⟩ : ↥N) : ↥N ⧸ Y₀.subgroupOf N) = QuotientGroup.mk n
    rw [QuotientGroup.eq, mem_subgroupOf]
    show k⁻¹ * (n : G) ∈ Y₀
    rw [hnkw, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hw
  have hker : φ.ker = CFSG.pCore 2 ↥(centPair z t) := by
    ext k
    rw [MonoidHom.mem_ker, mem_pCore_iff_mem_O2In]
    show (QuotientGroup.mk (⟨k, hKN k.2⟩ : ↥N) : ↥N ⧸ Y₀.subgroupOf N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact ⟨fun h => hg.inf_le (mem_inf.2 ⟨k.2, h⟩), fun h => hg.O2K_le h⟩
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans e⟩

section Certified


theorem Level55.good_of_le (d : Level55 G t z) {N : Subgroup G} (hKN : centPair z t ≤ N)
    (hNK : N ≤ centPair z t) : d.Good N (O2In (centPair z t)) where
  le := (O2In_le _).trans hKN
  normal := fun _ hn u hu => d.conj_O2K (hNK hn) u hu
  pgroup := isPGroup_O2In _
  O2K_le := le_rfl
  inf_le := inf_le_right
  decomp := fun n hn => ⟨n, hNK hn, 1, one_mem _, (mul_one n).symm⟩
  comm := fun _ ha _ hb => d.O2K_commutator_mem_zpowers ha hb
  cent := fun _ hn h => d.mem_O2K_of_comm_mem_zpowers (hNK hn) h

end Certified

section Certified2


theorem Level55.good_of_exists (d : Level55 G t z) {N : Subgroup G} (hKN : centPair z t ≤ N)
    (hNC : N ≤ centZ z) (hNn : N ≤ normPair z t) {x0 : G} (hx0 : x0 ∈ N)
    (hx0K : x0 ∉ centPair z t) : ∃ Y₀ : Subgroup G, d.Good N Y₀ := by
  obtain ⟨e⟩ := d.quot
  have hidx := d.relIndex_centPair_eq_two hNC hNn hx0 hx0K
  have hRC : ((O2In (centPair z t)).subgroupOf N).Normal :=
    ⟨fun u hu g => conj_mem_O2In_centPair_of_mem_normPair (hNn g.2) (mem_subgroupOf.1 hu)⟩
  obtain ⟨x, hxN, hxK, hxc, hx2⟩ := exists_lift_centralizing_co2 hKN hidx hRC e
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 (hNC hxN)
  have hxt : x * t * x⁻¹ = t * z := (d.conj_t_of_mem_normPair hxz (hNn hxN)).resolve_left
    (fun h => hxK (mem_centPair_of_conj_t hxz h))
  have hxnorm : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun y hy => conj_mem_O2In_centPair_of_mem_normPair (hNn hxN) hy
  have hxr : ∀ r ∈ O2In (centPair z t), x * r * x⁻¹ * r⁻¹ ∈ zpowers z :=
    d.comm_mem_zpowers hxz hxt hxnorm hxc hx2
  have hZc : ∀ g ∈ N, ∀ c ∈ zpowers z, g * c * g⁻¹ ∈ zpowers z := fun g hg c hc =>
    conj_mem_zpowers_of_conj_mem (b := z) (by
      rw [mem_centralizer_singleton_iff.1 (hNC hg), mul_inv_cancel_right]
      exact mem_zpowers z) c hc
  have hdich : ∀ n ∈ N, n ∈ centPair z t ∨ n * x ∈ centPair z t := fun n hn =>
    d.mem_centPair_or_mul_mem hxz hxt (mem_centralizer_singleton_iff.1 (hNC hn)) (hNn hn)
  have hxK' : ∀ k ∈ centPair z t, k * x * k⁻¹ ∈ O2In (centPair z t) ⊔ zpowers x := by
    intro k hk
    have h1 : (x * k * x⁻¹ * k⁻¹)⁻¹ ∈ O2In (centPair z t) := inv_mem (hxc k hk)
    have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
    rw [e]
    exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers x))
  have hnx : ∀ n ∈ N, n * x * n⁻¹ ∈ O2In (centPair z t) ⊔ zpowers x := by
    intro n hn
    rcases hdich n hn with h | h
    · exact hxK' n h
    · have := hxK' _ h
      have e : n * x * x * (n * x)⁻¹ = n * x * n⁻¹ := by group
      rwa [e] at this
  have hYN : ∀ r ∈ O2In (centPair z t), r ∈ N := fun r hr => hKN (O2In_le _ hr)
  have I1 : ∀ a b c : G, a * b * c * (a * b)⁻¹ * c⁻¹ =
      (a * (b * c * b⁻¹ * c⁻¹) * a⁻¹) * (a * c * a⁻¹ * c⁻¹) := by intros; group
  have I2 : ∀ a b c : G, a * (b * c) * a⁻¹ * (b * c)⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by intros; group
  have hrx : ∀ r ∈ O2In (centPair z t), r * x * r⁻¹ * x⁻¹ ∈ zpowers z := by
    intro r hr
    have e : r * x * r⁻¹ * x⁻¹ = (x * r * x⁻¹ * r⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hxr r hr)
  have hr1 : ∀ r ∈ O2In (centPair z t), ∀ r' ∈ O2In (centPair z t),
      r * (r' * x) * r⁻¹ * (r' * x)⁻¹ ∈ zpowers z := by
    intro r hr r' hr'
    rw [I2]
    exact mul_mem (d.O2K_commutator_mem_zpowers hr hr') (hZc r' (hYN r' hr') _ (hrx r hr))
  refine ⟨O2In (centPair z t) ⊔ zpowers x, ?_⟩
  exact
  { le := sup_le ((O2In_le _).trans hKN) (zpowers_le.2 hxN)
    normal := fun n hn u hu => conj_mem_sup_of_conj_mem
      (fun a ha => mem_sup_left (conj_mem_O2In_centPair_of_mem_normPair (hNn hn) ha))
      (conj_mem_zpowers_of_conj_mem (hnx n hn)) u hu
    pgroup := isPGroup_sup_zpowers_of_sq_mem (isPGroup_O2In _) hxnorm hx2
    O2K_le := le_sup_left
    inf_le := fun u hu => by
      obtain ⟨huK, huY⟩ := mem_inf.1 hu
      rcases mem_or_exists_mul_of_mem_sup_zpowers hxnorm hx2 huY with h | ⟨r, hr, rfl⟩
      · exact h
      · exfalso
        apply hxK
        have : x = r⁻¹ * (r * x) := by group
        rw [this]
        exact mul_mem (inv_mem (O2In_le _ hr)) huK
    decomp := fun n hn => by
      rcases hdich n hn with h | h
      · exact ⟨n, h, 1, one_mem _, (mul_one n).symm⟩
      · exact ⟨n * x, h, x⁻¹, inv_mem (mem_sup_right (mem_zpowers x)), by group⟩
    comm := fun a ha b hb => by
      rcases mem_or_exists_mul_of_mem_sup_zpowers hxnorm hx2 ha with ha | ⟨r, hr, rfl⟩ <;>
        rcases mem_or_exists_mul_of_mem_sup_zpowers hxnorm hx2 hb with hb | ⟨r', hr', rfl⟩
      · exact d.O2K_commutator_mem_zpowers ha hb
      · exact hr1 a ha r' hr'
      · rw [I1 r x b]
        exact mul_mem (hZc r (hYN r hr) _ (hxr b hb)) (d.O2K_commutator_mem_zpowers hr hb)
      · rw [I1 r x (r' * x)]
        have e : x * (r' * x) * x⁻¹ * (r' * x)⁻¹ = x * r' * x⁻¹ * r'⁻¹ := by group
        rw [e]
        exact mul_mem (hZc r (hYN r hr) _ (hxr r' hr')) (hr1 r hr r' hr')
    cent := fun n hn h => by
      rcases hdich n hn with hK | hK
      · exact mem_sup_left (d.mem_O2K_of_comm_mem_zpowers hK fun y hy => h y (mem_sup_left hy))
      · have hk : n * x ∈ O2In (centPair z t) := by
          refine d.mem_O2K_of_comm_mem_zpowers hK fun y hy => ?_
          rw [I1 n x y]
          exact mul_mem (hZc n hn _ (hxr y hy)) (h y (mem_sup_left hy))
        have : n = (n * x) * x⁻¹ := by group
        rw [this]
        exact mul_mem (mem_sup_left hk) (inv_mem (mem_sup_right (mem_zpowers x))) }


theorem Level55.exists_good (d : Level55 G t z) {N : Subgroup G} (hKN : centPair z t ≤ N)
    (hNC : N ≤ centZ z) (hNn : N ≤ normPair z t) : ∃ Y₀ : Subgroup G, d.Good N Y₀ := by
  by_cases hN : N ≤ centPair z t
  · exact ⟨_, d.good_of_le hKN hN⟩
  · obtain ⟨x0, hx0, hx0K⟩ := IsConcreteLE.not_le_iff_exists.1 hN
    exact d.good_of_exists hKN hNC hNn hx0 hx0K

end Certified2

end CFSG.EvenSporadicStandard.TwoB
