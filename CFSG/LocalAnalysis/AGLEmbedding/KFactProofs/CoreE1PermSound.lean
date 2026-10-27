module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreE1Defs
public import Certificates.Data.CoreE1Perm
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding.CoreE1

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreE1Perm
open Certificates.FusD2Perm (powT wordT)
open CFSG.AGLEmbedding.FusD2 (wordVal wordVal_mem powT_rep)

section Transport

private theorem map_map_symm {K L : Type*} [Group K] [Group L] (e : K ≃* L) (H : Subgroup K) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  rw [this, Subgroup.map_id]

variable {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]

private theorem glbCore_map_le (p k : ℕ) (hp : 1 < p) (e : K ≃* L) (P : Subgroup K) :
    (GLBCore p k P).map e.toMonoidHom ≤ GLBCore p k (P.map e.toMonoidHom) := by
  unfold GLBCore
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hQk, rfl⟩
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
  exact le_sSup ⟨Q.map e.toMonoidHom, Subgroup.map_mono hQP,
    hQk.trans (CFSG.SectionRank.pRank_le_map hp e.toMonoidHom e.injective Q), rfl⟩

private theorem movesCentre_map (e : K ≃* L) {T E : Subgroup K} (h : MovesCentre K T E) :
    MovesCentre L (T.map e.toMonoidHom) (E.map e.toMonoidHom) := by
  obtain ⟨z, hzT, hz1, hzc, hzg, h', hh', hne, hcop⟩ := h
  refine ⟨e z, Subgroup.mem_map_of_mem e.toMonoidHom hzT,
    fun h1 => hz1 (e.injective (h1.trans (map_one e).symm)), ?_, ?_, e h',
    glbCore_map_le 3 1 (by norm_num) e E (Subgroup.mem_map_of_mem e.toMonoidHom hh'), ?_, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hzc t' ht']
  · intro w hw hwc
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    simp only [MulEquiv.coe_toMonoidHom] at hwc ⊢
    have hw'z : w' ∈ Subgroup.zpowers z := by
      refine hzg w' hw' fun t ht => e.injective ?_
      rw [map_mul, map_mul]
      exact hwc (e t) (Subgroup.mem_map_of_mem e.toMonoidHom ht)
    have := Subgroup.mem_map_of_mem e.toMonoidHom hw'z
    rwa [MonoidHom.map_zpowers] at this
  · intro h1
    refine hne (e.injective ?_)
    rw [map_one, ← h1]
    simp
  · have h2 := hcop
    rw [← MulEquiv.orderOf_eq e] at h2
    simpa using h2

private theorem transitiveOn_map (e : K ≃* L) {E : Subgroup K} (h : TransitiveOn K E) :
    TransitiveOn L (E.map e.toMonoidHom) := by
  intro u hu v hv hu1 hv1
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hv
  simp only [MulEquiv.coe_toMonoidHom] at hu1 hv1 ⊢
  obtain ⟨n, hn, hnu⟩ := h u' hu' v' hv'
    (fun h1 => hu1 (by rw [h1, map_one])) (fun h1 => hv1 (by rw [h1, map_one]))
  refine ⟨e n, ?_, ?_⟩
  · have := Subgroup.mem_map_of_mem e.toMonoidHom hn
    rwa [Subgroup.map_equiv_normalizer_eq] at this
  · rw [← map_mul, ← map_inv, ← map_mul, hnu]

private def DatumAt (K : Type*) [Group K] [Finite K] (T : Subgroup K) : Prop :=
  Nat.card T = 27 ∧ (∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) ∧
    ∀ E : Subgroup K, E ≤ T → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      MovesCentre K T E ∨ TransitiveOn K E

private theorem DatumAt.map (e : K ≃* L) {T : Subgroup K} (h : DatumAt K T) :
    DatumAt L (T.map e.toMonoidHom) := by
  obtain ⟨hc, ⟨x, hx, y, hy, hxy⟩, hE⟩ := h
  refine ⟨?_, ⟨e x, Subgroup.mem_map_of_mem e.toMonoidHom hx, e y,
    Subgroup.mem_map_of_mem e.toMonoidHom hy, fun h1 => hxy (e.injective ?_)⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hc
  · rw [map_mul, map_mul]
    exact h1
  · intro E' hE'T hE'e hE'c
    have hET : E'.map e.symm.toMonoidHom ≤ T := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hE'T
      rwa [map_map_symm] at this
    have hEE : (E'.map e.symm.toMonoidHom).map e.toMonoidHom = E' := by
      have := map_map_symm e.symm E'
      rwa [MulEquiv.symm_symm] at this
    have hEe : IsElemAbelian 3 (E'.map e.symm.toMonoidHom) := hE'e.map e.symm.toMonoidHom
    have hEc : Nat.card (E'.map e.symm.toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective e.symm.injective]
      exact hE'c
    rcases hE _ hET hEe hEc with h1 | h1
    · left
      have := movesCentre_map e h1
      rwa [hEE] at this
    · right
      have := transitiveOn_map e h1
      rwa [hEE] at this

theorem Datum.of_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] [Finite L] (e : K ≃* L)
    (h : Datum L) : Datum K := by
  intro T
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : DatumAt L (T.map e.toMonoidHom) :=
    h (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  have h2 := DatumAt.map e.symm h1
  rw [map_map_symm] at h2
  exact h2

private theorem datum_of_sylow (S : Sylow 3 K) (h : DatumAt K S) : Datum K := by
  intro T
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S T
  have h1 := DatumAt.map (MulAut.conj g) h
  have h2 : (S : Subgroup K).map (MulAut.conj g).toMonoidHom = T := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [h2] at h1
  exact h1

end Transport

section Abstract

variable {X : Type*} [Group X]

private theorem isElemAbelian_closure_pair {p : ℕ} {u v : X} (hu : u ^ p = 1) (hv : v ^ p = 1)
    (huv : u * v = v * u) : IsElemAbelian p (Subgroup.closure ({u, v} : Set X)) := by
  have hrc : ({u, v} : Set X).Pairwise Commute := by
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · exact absurd rfl hab
    · exact huv
    · exact huv.symm
    · exact absurd rfl hab
  have := Subgroup.isMulCommutative_closure hrc
  refine ⟨this, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    exacts [hu, hv]
  | one => exact one_pow p
  | mul x y hx hy hx' hy' =>
    rw [(show Commute x y from setLike_mul_comm hx hy).mul_pow, hx', hy', one_mul]
  | inv x hx hx' => rw [inv_pow, hx', inv_one]

private theorem card_closure_pair {p : ℕ} (hp : p.Prime) {a b : X} (hab : Commute a b)
    (ha : orderOf a = p) (hb : orderOf b = p) (hind : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set X)) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  have hcb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hca : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hcb]; exact hp⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases h with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hbb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) ∈
          (Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hbb).1
  let φ : Subgroup.zpowers a × Subgroup.zpowers b →* X :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : X) * y = 1 := hxy
    have hx : (x : X) = (y : X)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : X) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers b).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : X) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set X) := by
    have h1 : φ.range = (Subgroup.zpowers a).subtype.range ⊔ (Subgroup.zpowers b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype, Set.insert_eq,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hca, hcb,
    sq]

private theorem mem_normalizer_closure_pair [Finite X] {u v g : X} {α β γ δ : ℕ}
    (h1 : g * u = (u ^ α * v ^ β) * g) (h2 : g * v = (u ^ γ * v ^ δ) * g) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({u, v} : Set X) : Subgroup X) : Set X) := by
  have hu : u ∈ Subgroup.closure ({u, v} : Set X) := Subgroup.subset_closure (by simp)
  have hv : v ∈ Subgroup.closure ({u, v} : Set X) := Subgroup.subset_closure (by simp)
  have hcu : g * u * g⁻¹ ∈ Subgroup.closure ({u, v} : Set X) := by
    rw [mul_inv_eq_iff_eq_mul.2 h1]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hu _) (Subgroup.pow_mem _ hv _)
  have hcv : g * v * g⁻¹ ∈ Subgroup.closure ({u, v} : Set X) := by
    rw [mul_inv_eq_iff_eq_mul.2 h2]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hu _) (Subgroup.pow_mem _ hv _)
  have hle : Subgroup.closure ({u, v} : Set X) ≤
      (Subgroup.closure ({u, v} : Set X)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hcu, hcv⟩
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

private theorem mem_normalizer_zpowers_of_mul_eq [Finite X] {u g : X} {α : ℕ}
    (h : g * u = u ^ α * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup X) : Set X) := by
  have hcu : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
    rw [mul_inv_eq_iff_eq_mul.2 h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _
  have hle : Subgroup.zpowers u ≤ (Subgroup.zpowers u).comap (MulAut.conj g).toMonoidHom :=
    Subgroup.zpowers_le.2 hcu
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

private theorem mem_of_central [Finite X] {p : ℕ} (hp : p.Prime) {E A : Subgroup X}
    (hEc : Nat.card E = p ^ 3) (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (hAE : A ≤ E)
    (hAe : IsElemAbelian p A) (hA : Nat.card A = p ^ 2) {u : X} (huE : u ∈ E)
    (hu : ∀ x ∈ E, x * u = u * x) : u ∈ A := by
  by_contra huA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hrc : ((A : Set X) ∪ {u}).Pairwise Commute := by
    rintro x (hx | hx) y (hy | hy) hxy
    · exact hcomm x hx y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hu x (hAE hx)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hu y (hAE hy)).symm
    · rw [Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  have hBcomm := Subgroup.isMulCommutative_closure hrc
  set B := Subgroup.closure ((A : Set X) ∪ {u}) with hB
  have hAB : A ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have huB : u ∈ B := Subgroup.subset_closure (Or.inr rfl)
  have hBE : B ≤ E := by
    rw [hB, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hAE hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact huE
  have hd1 : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hd2 : Nat.card B ∣ p ^ 3 := hEc ▸ Subgroup.card_dvd_of_le hBE
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow hp).1 hd2
  rw [hA, hm] at hd1
  have hm2 : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd1
  have hm' : m = 2 ∨ m = 3 := by omega
  rcases hm' with rfl | rfl
  · have : A = B := Subgroup.eq_of_le_of_card_ge hAB (by rw [hA, hm])
    exact huA (this ▸ huB)
  · have : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hEc, hm])
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    rw [← this] at hx hy
    exact hxy (congrArg Subtype.val (hBcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

private theorem mem_closure_pair {z x u : X} (hz : z ^ 3 = 1) (hx : x ^ 3 = 1)
    (hzx : z * x = x * z) (hu : u ∈ Subgroup.closure ({z, x} : Set X)) :
    ∃ a < 3, ∃ b < 3, u = z ^ a * x ^ b := by
  have hc : ∀ a b : ℕ, x ^ b * z ^ a = z ^ a * x ^ b := fun a b =>
    (Commute.pow_pow hzx.symm b a).eq
  have hinvz : ∀ a : ℕ, (z ^ a)⁻¹ = z ^ (2 * a) := fun a => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, show a + 2 * a = 3 * a by ring, pow_mul, hz, one_pow]
  have hinvx : ∀ b : ℕ, (x ^ b)⁻¹ = x ^ (2 * b) := fun b => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, show b + 2 * b = 3 * b by ring, pow_mul, hx, one_pow]
  have key : ∃ a b : ℕ, u = z ^ a * x ^ b := by
    induction hu using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul s t _ _ hs ht =>
      obtain ⟨a, b, rfl⟩ := hs
      obtain ⟨a', b', rfl⟩ := ht
      refine ⟨a + a', b + b', ?_⟩
      rw [pow_add, pow_add]
      calc z ^ a * x ^ b * (z ^ a' * x ^ b') = z ^ a * (x ^ b * z ^ a') * x ^ b' := by
            simp only [mul_assoc]
        _ = z ^ a * (z ^ a' * x ^ b) * x ^ b' := by rw [hc a' b]
        _ = z ^ a * z ^ a' * (x ^ b * x ^ b') := by simp only [mul_assoc]
    | inv s _ hs =>
      obtain ⟨a, b, rfl⟩ := hs
      refine ⟨2 * a, 2 * b, ?_⟩
      rw [mul_inv_rev, hinvz, hinvx, hc]
  obtain ⟨a, b, rfl⟩ := key
  exact ⟨a % 3, Nat.mod_lt _ (by norm_num), b % 3, Nat.mod_lt _ (by norm_num),
    by rw [← pow_eq_pow_mod a hz, ← pow_eq_pow_mod b hx]⟩

private theorem closure_pair_facts {z x : X} (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1) (hz1 : z ≠ 1)
    (hxz : x * z = z * x) (hxn : x ∉ Subgroup.zpowers z) :
    IsElemAbelian 3 (Subgroup.closure ({z, x} : Set X)) ∧
      Nat.card (Subgroup.closure ({z, x} : Set X)) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => hxn (h ▸ Subgroup.one_mem _)
  exact ⟨isElemAbelian_closure_pair hz3 hx3 hxz.symm,
    card_closure_pair Nat.prime_three hxz.symm (orderOf_eq_prime hz3 hz1)
      (orderOf_eq_prime hx3 hx1) hxn⟩

private theorem normalizer_le_glbCore [Finite X] {p k : ℕ} {P Q : Subgroup X} (hQP : Q ≤ P)
    (hQk : k ≤ Open.pRank p Q) : Subgroup.normalizer (Q : Set X) ≤ GLBCore p k P :=
  le_sSup ⟨Q, hQP, hQk, rfl⟩

private theorem mem_glbCore_of_zpowers [Finite X] {E : Subgroup X} {u g : X} (huE : u ∈ E)
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) {α : ℕ} (hg : g * u = u ^ α * g) :
    g ∈ GLBCore 3 1 E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : 1 ≤ Open.pRank 3 (Subgroup.zpowers u) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_zpowers hu3)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1, pow_one])
  exact normalizer_le_glbCore (Subgroup.zpowers_le.2 huE) hr (mem_normalizer_zpowers_of_mul_eq hg)

private theorem mem_glbCore_of_normalizer [Finite X] {E : Subgroup X} {g : X}
    (hE : 1 ≤ Open.pRank 3 E) (hg : g ∈ Subgroup.normalizer (E : Set X)) : g ∈ GLBCore 3 1 E :=
  normalizer_le_glbCore le_rfl hE hg

private structure Core (S : Subgroup X) (z : X) (m : ℕ) (x : ℕ → X) : Prop where
  card : Nat.card S = 3 ^ 3
  noncomm : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a
  z_mem : z ∈ S
  z_ne : z ≠ 1
  z_pow : z ^ 3 = 1
  z_comm : ∀ t ∈ S, t * z = z * t
  z_gen : ∀ w ∈ S, (∀ t ∈ S, t * w = w * t) → w ∈ Subgroup.zpowers z
  x_pow : ∀ i < m, x i ^ 3 = 1
  x_comm : ∀ i < m, x i * z = z * x i
  x_not : ∀ i < m, x i ∉ Subgroup.zpowers z
  cover : ∀ s ∈ S, ∃ i < m, ∃ a < 3, ∃ b < 3, s = z ^ a * x i ^ b

private theorem Core.exists_index [Finite X] {S : Subgroup X} {z : X} {m : ℕ} {x : ℕ → X}
    (hc : Core S z m x) {E : Subgroup X} (hES : E ≤ S) (hEe : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) : ∃ i < m, E = Subgroup.closure ({z, x i} : Set X) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hzE : z ∈ E := mem_of_central hp hc.card hc.noncomm hES hEe hEc hc.z_mem hc.z_comm
  have hzord : orderOf z = 3 := orderOf_eq_prime hc.z_pow hc.z_ne
  obtain ⟨s, hsE, hsz⟩ : ∃ s ∈ E, s ∉ Subgroup.zpowers z := by
    by_contra hcon
    have hle : E ≤ Subgroup.zpowers z := fun s hs => by
      by_contra hs'
      exact hcon ⟨s, hs, hs'⟩
    have := Subgroup.card_le_of_le hle
    rw [hEc, Nat.card_zpowers, hzord] at this
    omega
  obtain ⟨i, hi, a, ha, b, hb, hsab⟩ := hc.cover s (hES hsE)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hsz (by rw [hsab, pow_zero, mul_one]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)
  have hxb : x i ^ b ∈ E := by
    have : x i ^ b = (z ^ a)⁻¹ * s := by rw [hsab]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hzE _)) hsE
  have hxE : x i ∈ E := by
    have hx3 := hc.x_pow i hi
    have hb' : b = 1 ∨ b = 2 := by omega
    rcases hb' with rfl | rfl
    · simpa using hxb
    · have : x i = (x i ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
      rw [this]
      exact Subgroup.pow_mem _ hxb _
  have hle : Subgroup.closure ({z, x i} : Set X) ≤ E := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzE, hxE⟩
  obtain ⟨-, hcard⟩ := closure_pair_facts hc.z_pow (hc.x_pow i hi) hc.z_ne (hc.x_comm i hi)
    (hc.x_not i hi)
  exact ⟨i, hi, (Subgroup.eq_of_le_of_card_ge hle (by rw [hEc, hcard])).symm⟩

private theorem movesCentre_of [Finite X] {S E : Subgroup X} {z : X} (hzS : z ∈ S) (hz1 : z ≠ 1)
    (hzc : ∀ t ∈ S, t * z = z * t)
    (hzg : ∀ w ∈ S, (∀ t ∈ S, t * w = w * t) → w ∈ Subgroup.zpowers z) {h : X}
    (hh : h ∈ GLBCore 3 1 E) {m : ℕ} (hne : z * (h * z * h⁻¹) ≠ 1)
    (hpow : (z * (h * z * h⁻¹)) ^ m = 1) (hm : ¬ 3 ∣ m) : MovesCentre X S E :=
  ⟨z, hzS, hz1, hzc, hzg, h, hh, hne, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
    fun h3 => hm (h3.trans (orderOf_dvd_of_pow_eq_one hpow))⟩

private theorem transitiveOn_of [Finite X] {z x : X} (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1)
    (hzx : z * x = x * z) {gs : List X}
    (hgs : ∀ g ∈ gs,
      g ∈ Subgroup.normalizer ((Subgroup.closure ({z, x} : Set X) : Subgroup X) : Set X))
    (tW : ℕ → List ℤ)
    (ht : ∀ k, 0 < k → k < 9 →
      wordVal gs (tW k) * z = (z ^ (k / 3) * x ^ (k % 3)) * wordVal gs (tW k)) :
    TransitiveOn X (Subgroup.closure ({z, x} : Set X)) := by
  set E := Subgroup.closure ({z, x} : Set X) with hE
  have hw : ∀ u ∈ E, u ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * z * w⁻¹ = u := by
    intro u hu hu1
    obtain ⟨a, ha, b, hb, hab⟩ := mem_closure_pair hz3 hx3 hzx hu
    have hk0 : 0 < 3 * a + b := by
      by_contra hcon
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      exact hu1 (by rw [hab, ha0, hb0]; simp)
    have hk9 : 3 * a + b < 9 := by omega
    have hk3 : (3 * a + b) / 3 = a := by omega
    have hkm : (3 * a + b) % 3 = b := by omega
    refine ⟨wordVal gs (tW (3 * a + b)),
      wordVal_mem gs (Subgroup.normalizer (E : Set X)) hgs _, ?_⟩
    have := ht (3 * a + b) hk0 hk9
    rw [hk3, hkm, ← hab] at this
    exact mul_inv_eq_iff_eq_mul.2 this
  intro u hu v hv hu1 hv1
  obtain ⟨wu, hwu, hwuz⟩ := hw u hu hu1
  obtain ⟨wv, hwv, hwvz⟩ := hw v hv hv1
  refine ⟨wv * wu⁻¹, (Subgroup.normalizer (E : Set X)).mul_mem hwv
    ((Subgroup.normalizer (E : Set X)).inv_mem hwu), ?_⟩
  rw [← hwuz, ← hwvz]
  group

private theorem Core.datumAt [Finite X] {S : Subgroup X} {z : X} {m : ℕ} {x : ℕ → X}
    (hc : Core S z m x)
    (hent : ∀ i < m, MovesCentre X S (Subgroup.closure ({z, x i} : Set X)) ∨
      TransitiveOn X (Subgroup.closure ({z, x i} : Set X))) : DatumAt X S := by
  refine ⟨by rw [hc.card]; norm_num, hc.noncomm, fun E hES hEe hEc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := hc.exists_index hES hEe hEc
  exact hent i hi

private theorem exists_pow_of_mem_zpowers [Finite X] {z x : X} (hz : z ^ 3 = 1)
    (h : x ∈ Subgroup.zpowers z) : ∃ a < 3, x = z ^ a := by
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m % 3, Nat.mod_lt _ (by norm_num), by rw [← hm, ← pow_eq_pow_mod m hz]⟩

end Abstract

section Tables

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

private theorem tabRep_mul {t s : Tab} {k l : ↥G} (hk : TabRep t (k : Equiv.Perm (Fin n)))
    (hl : TabRep s (l : Equiv.Perm (Fin n))) :
    TabRep (comp n t s) ((k * l : ↥G) : Equiv.Perm (Fin n)) := by
  rw [Subgroup.coe_mul]
  exact hk.comp hl

private theorem tabRep_pow {t : Tab} {k : ↥G} (hk : TabRep t (k : Equiv.Perm (Fin n))) (m : ℕ) :
    TabRep (powT n t m) ((k ^ m : ↥G) : Equiv.Perm (Fin n)) := by
  rw [Subgroup.coe_pow]
  exact powT_rep hk m

private theorem tabRep_one : TabRep (idTab n) ((1 : ↥G) : Equiv.Perm (Fin n)) := by
  rw [Subgroup.coe_one]
  exact TabRep.idTab

private theorem tabRep_inv {t s : Tab} {k : ↥G} (hk : TabRep t (k : Equiv.Perm (Fin n)))
    (hs : s.size = n) (hc : comp n s t = idTab n) :
    TabRep s ((k⁻¹ : ↥G) : Equiv.Perm (Fin n)) := by
  rw [Subgroup.coe_inv]
  exact hk.inv hs hc

private theorem tabRep_eq_iff {t t' : Tab} {k l : ↥G} (hk : TabRep t (k : Equiv.Perm (Fin n)))
    (hl : TabRep t' (l : Equiv.Perm (Fin n))) : t = t' ↔ k = l :=
  (hk.eq_iff hl).trans Subtype.ext_iff.symm

private theorem wordT_repK (S : List ↥G) (gs gi : Array Tab)
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) ((S.getD j 1 : ↥G) : Equiv.Perm (Fin n)))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) ((S.getD j 1 : ↥G) : Equiv.Perm (Fin n))⁻¹)
    (w : List ℤ) : TabRep (wordT n gs gi w) ((wordVal S w : ↥G) : Equiv.Perm (Fin n)) := by
  induction w with
  | nil =>
    rw [wordT, wordVal, Subgroup.coe_one]
    exact TabRep.idTab
  | cons z w ih =>
    rw [wordT, wordVal, Subgroup.coe_mul]
    refine TabRep.comp ?_ ih
    split_ifs
    · exact hgs _
    · rw [Subgroup.coe_inv]
      exact hgi _

private theorem rep_mapK (F : List ℤ → Tab) (wv : List ℤ → ↥G)
    (hF : ∀ w, TabRep (F w) ((wv w : ↥G) : Equiv.Perm (Fin n))) (ws : List (List ℤ)) (j : ℕ) :
    TabRep ((ws.map F).toArray.getD j (idTab n))
      (((ws.map wv).getD j 1 : ↥G) : Equiv.Perm (Fin n)) := by
  by_cases hj : j < ws.length
  · rw [show (ws.map F).toArray.getD j (idTab n) = F ws[j] by simp [hj],
      show (ws.map wv).getD j 1 = wv ws[j] by simp [hj]]
    exact hF _
  · have hn : ws[j]? = none := List.getElem?_eq_none (by omega)
    rw [show (ws.map F).toArray.getD j (idTab n) = idTab n by simp [hn],
      show (ws.map wv).getD j 1 = 1 by simp [hn]]
    exact tabRep_one

private theorem rep_invK (T : Array Tab) (S : List ↥G)
    (hT : ∀ j, TabRep (T.getD j (idTab n)) ((S.getD j 1 : ↥G) : Equiv.Perm (Fin n)))
    (hsize : T.size = S.length)
    (hinv : ∀ j < T.size, (T.map (invTab n))[j]!.size = n ∧
      comp n (T.map (invTab n))[j]! T[j]! = idTab n) :
    ∀ j, TabRep ((T.map (invTab n)).getD j (idTab n))
      ((S.getD j 1 : ↥G) : Equiv.Perm (Fin n))⁻¹ := by
  intro j
  by_cases hj : j < T.size
  · obtain ⟨h1, h2⟩ := hinv j hj
    rw [show (T.map (invTab n)).getD j (idTab n) = (T.map (invTab n))[j]! by simp [hj]]
    have := hT j
    rw [show T.getD j (idTab n) = T[j]! by simp [hj]] at this
    rw [← Subgroup.coe_inv]
    exact tabRep_inv this h1 h2
  · have hS : S[j]? = none := List.getElem?_eq_none (by omega)
    rw [show (T.map (invTab n)).getD j (idTab n) = idTab n by simp [hj],
      show S.getD j 1 = 1 by simp [hS]]
    simpa using TabRep.idTab (n := n)

private theorem mem_toList_of_contains {T : Array Tab} {t : Tab} (h : T.contains t = true) :
    t ∈ T.toList :=
  Array.mem_def.1 (Array.contains_iff.1 h)

private theorem all_toList {T : Array Tab} {p : Tab → Bool} (h : T.all p = true) :
    ∀ t ∈ T.toList, p t = true := fun t ht =>
  Array.all_eq_true_iff_forall_mem.1 h t (Array.mem_def.2 ht)

private theorem exists_mem_of_any {T : Array Tab} {p : Tab → Bool} (h : T.any p = true) :
    ∃ t ∈ T.toList, p t = true := by
  obtain ⟨i, hi, hp⟩ := Array.any_eq_true.1 h
  exact ⟨T[i], by simp, hp⟩

end Tables

section Decode

variable {D : Data} {G : Subgroup (Equiv.Perm (Fin D.n))}

private theorem mem_sGens_iff {t : Tab} : t ∈ sGens D ↔ ∃ w ∈ D.sW, wT D w = t := by
  rw [Array.mem_def]
  simp [sGens]

private theorem core_of_check (wv : List ℤ → ↥G)
    (hwT : ∀ w, TabRep (wT D w) ((wv w : ↥G) : Equiv.Perm (Fin D.n)))
    (hs : sOK D = true) (hz : zOK D = true) (hx : xOK D = true) :
    Core (Subgroup.closure {g | g ∈ D.sW.map wv}) (wv D.zW) D.xWs.length
      (fun i => wv (D.xWs.getD i [])) := by
  set L : List ↥G := D.sW.map wv with hL
  set S : Subgroup ↥G := Subgroup.closure {g | g ∈ L} with hS
  have hzt : TabRep (zT D) ((wv D.zW : ↥G) : Equiv.Perm (Fin D.n)) := hwT _
  have hxt : ∀ i, TabRep (xT D i) ((wv (D.xWs.getD i []) : ↥G) : Equiv.Perm (Fin D.n)) :=
    fun i => hwT _
  simp only [sOK, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨henum, hsz⟩, hnc⟩ := hs
  have hgs : ∀ j, TabRep ((sGens D).getD j (idTab D.n))
      ((L.getD j 1 : ↥G) : Equiv.Perm (Fin D.n)) := rep_mapK (wT D) wv hwT D.sW
  have hEsz : (sGens D).size = D.sW.length := by simp [sGens]
  have hLlen : L.length = D.sW.length := by simp [hL]
  have hgs' : ∀ j (hj : j < D.sW.length),
      TabRep (sGens D)[j]! ((L.getD j 1 : ↥G) : Equiv.Perm (Fin D.n)) := by
    intro j hj
    have := hgs j
    rwa [show (sGens D).getD j (idTab D.n) = (sGens D)[j]! by simp [sGens, hj]] at this
  have hLmem : ∀ j, j < D.sW.length → L.getD j 1 ∈ L := by
    intro j hj
    rw [show L.getD j 1 = L[j]'(by omega) by simp [List.getD_eq_getElem?_getD, hLlen, hj]]
    exact List.getElem_mem _
  have hA : ∀ g ∈ G.subtype '' {g | g ∈ L}, ∃ j < (sGens D).size,
      TabRep (sGens D)[j]! g := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < D.sW.length := by omega
    refine ⟨j, by rw [hEsz]; exact hj', ?_⟩
    have := hgs' j hj'
    rwa [show L.getD j 1 = L[j] by simp [hj]] at this
  have hgensE : ∀ j < (sGens D).size, ∃ g ∈ G.subtype '' {g | g ∈ L},
      TabRep (sGens D)[j]! g := by
    intro j hj
    have hj' : j < D.sW.length := by rwa [hEsz] at hj
    exact ⟨_, ⟨L.getD j 1, hLmem j hj', rfl⟩, hgs' j hj'⟩
  have hE := enumerates_closure (A := G.subtype '' {g | g ∈ L}) hA hgensE henum
  have hSX : S.map G.subtype = Subgroup.closure (G.subtype '' {g | g ∈ L}) :=
    MonoidHom.map_closure _ _
  have hmemS : ∀ g : ↥G, g ∈ S ↔
      (g : Equiv.Perm (Fin D.n)) ∈ Subgroup.closure (G.subtype '' {g | g ∈ L}) := fun g => by
    rw [← hSX]
    exact (Subgroup.mem_map_iff_mem G.subtype_injective).symm
  have hcard : Nat.card S = 3 ^ 3 := by
    have h1 := hE.card
    rw [Array.length_toList, hsz, ← hSX, Subgroup.card_map_of_injective G.subtype_injective] at h1
    rw [h1]
    norm_num
  have hgenmem : ∀ w ∈ D.sW, wv w ∈ S := fun w hw =>
    Subgroup.subset_closure (List.mem_map.2 ⟨w, hw, rfl⟩)
  have hnc' : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
    obtain ⟨s, hs, hs'⟩ := exists_mem_of_any hnc
    obtain ⟨t, ht, ht'⟩ := exists_mem_of_any hs'
    obtain ⟨w1, hw1, rfl⟩ := mem_sGens_iff.1 (Array.mem_def.2 hs)
    obtain ⟨w2, hw2, rfl⟩ := mem_sGens_iff.1 (Array.mem_def.2 ht)
    refine ⟨wv w1, hgenmem w1 hw1, wv w2, hgenmem w2 hw2, fun h => ?_⟩
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at ht'
    exact ht' ((tabRep_eq_iff (tabRep_mul (hwT w1) (hwT w2))
      (tabRep_mul (hwT w2) (hwT w1))).2 h)
  simp only [zOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq] at hz
  obtain ⟨⟨⟨⟨hzin, hz1⟩, hz3⟩, hzcent⟩, hzall⟩ := hz
  have hzS : wv D.zW ∈ S := by
    obtain ⟨g, hg, hgt⟩ := hE.sound _ (mem_toList_of_contains hzin)
    rw [hmemS, hzt.perm_eq hgt]
    exact hg
  have hcommgen : ∀ w ∈ D.sW, wv D.zW * wv w = wv w * wv D.zW := by
    intro w hw
    have := Array.all_eq_true_iff_forall_mem.1 hzcent (wT D w) (mem_sGens_iff.2 ⟨w, hw, rfl⟩)
    exact (tabRep_eq_iff (tabRep_mul hzt (hwT w)) (tabRep_mul (hwT w) hzt)).1 (beq_iff_eq.1 this)
  have hzcomm : ∀ t ∈ S, t * wv D.zW = wv D.zW * t := by
    have hle : S ≤ Subgroup.centralizer {wv D.zW} := by
      rw [hS, Subgroup.closure_le]
      intro g hg
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact hcommgen w hw
    intro t ht
    exact (Subgroup.mem_centralizer_iff.1 (hle ht) (wv D.zW) rfl).symm
  have hzgen : ∀ w ∈ S, (∀ t ∈ S, t * w = w * t) → w ∈ Subgroup.zpowers (wv D.zW) := by
    intro w hw hwc
    obtain ⟨t, ht, hwt⟩ := hE.complete (w : Equiv.Perm (Fin D.n)) ((hmemS w).1 hw)
    have hcen : central D t = true := by
      refine Array.all_eq_true_iff_forall_mem.2 fun s hs => ?_
      obtain ⟨w', hw', rfl⟩ := mem_sGens_iff.1 hs
      refine beq_iff_eq.2 ?_
      exact (tabRep_eq_iff (tabRep_mul hwt (hwT w')) (tabRep_mul (hwT w') hwt)).2
        (hwc _ (hgenmem w' hw')).symm
    have h1 := all_toList hzall t ht
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · rw [hcen] at h1
      exact absurd h1 (by simp)
    · simp only [inZ, anyBelow_eq_true, beq_iff_eq] at h1
      obtain ⟨a, ha, hta⟩ := h1
      have : w = wv D.zW ^ a := (tabRep_eq_iff hwt (tabRep_pow hzt a)).1 hta
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hz3' : wv D.zW ^ 3 = 1 := (tabRep_eq_iff (tabRep_pow hzt 3) tabRep_one).1 hz3
  simp only [xOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Bool.not_eq_true'] at hx
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨hcard, hnc', hzS, fun h => hz1 ((tabRep_eq_iff hzt tabRep_one).2 h), hz3', hzcomm,
    hzgen, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (tabRep_eq_iff (tabRep_pow (hxt i) 3) tabRep_one).1 (hx1 i hi).1.1.2
  · intro i hi
    exact (tabRep_eq_iff (tabRep_mul (hxt i) hzt) (tabRep_mul hzt (hxt i))).1 (hx1 i hi).1.2
  · intro i hi hmem
    obtain ⟨a, ha, hxa⟩ := exists_pow_of_mem_zpowers hz3' hmem
    have h1 := (hx1 i hi).2
    have h2 : inZ D (xT D i) = true := by
      simp only [inZ, anyBelow_eq_true, beq_iff_eq]
      exact ⟨a, ha, (tabRep_eq_iff (hxt i) (tabRep_pow hzt a)).2 hxa⟩
    rw [h2] at h1
    exact absurd h1 (by simp)
  · intro s hsS
    obtain ⟨t, ht, hst⟩ := hE.complete (s : Equiv.Perm (Fin D.n)) ((hmemS s).1 hsS)
    have h1 := all_toList hx2 t ht
    simp only [anyBelow_eq_true] at h1
    obtain ⟨i, hi, h2⟩ := h1
    simp only [inE, anyBelow_eq_true, beq_iff_eq] at h2
    obtain ⟨a, ha, b, hb, hab⟩ := h2
    exact ⟨i, hi, a, ha, b, hb, (tabRep_eq_iff hst (tabRep_mul (tabRep_pow hzt a)
      (tabRep_pow (hxt i) b))).1 hab⟩

private theorem nrm_spec {i : ℕ} {z x k : ↥G}
    (hzt : TabRep (zT D) (z : Equiv.Perm (Fin D.n)))
    (hxt : TabRep (xT D i) (x : Equiv.Perm (Fin D.n))) {g : Tab}
    (hg : TabRep g (k : Equiv.Perm (Fin D.n))) {f : Nrm} (h : nrmOK D i g f = true) :
    (f.two = true → k * z = (z ^ f.α * x ^ f.β) * k ∧ k * x = (z ^ f.γ * x ^ f.δ) * k) ∧
    (f.two = false → z ^ f.a * x ^ f.b ≠ 1 ∧
      k * (z ^ f.a * x ^ f.b) = (z ^ f.a * x ^ f.b) ^ f.α * k) := by
  have hzx : ∀ a b, TabRep (zx D i a b) ((z ^ a * x ^ b : ↥G) : Equiv.Perm (Fin D.n)) :=
    fun a b => tabRep_mul (tabRep_pow hzt a) (tabRep_pow hxt b)
  unfold nrmOK at h
  constructor
  · intro h2
    rw [if_pos h2] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2'⟩ := h
    exact ⟨(tabRep_eq_iff (tabRep_mul hg hzt) (tabRep_mul (hzx _ _) hg)).1 h1,
      (tabRep_eq_iff (tabRep_mul hg hxt) (tabRep_mul (hzx _ _) hg)).1 h2'⟩
  · intro h2
    rw [if_neg (by simp [h2])] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨h1, h2'⟩ := h
    exact ⟨fun hu => h1 ((tabRep_eq_iff (hzx _ _) tabRep_one).2 hu),
      (tabRep_eq_iff (tabRep_mul hg (hzx _ _))
        (tabRep_mul (tabRep_pow (hzx _ _) _) hg)).1 h2'⟩

private theorem entry_sound (wv : List ℤ → ↥G)
    (hwT : ∀ w, TabRep (wT D w) ((wv w : ↥G) : Equiv.Perm (Fin D.n))) {S : Subgroup ↥G}
    (hc : Core S (wv D.zW) D.xWs.length (fun i => wv (D.xWs.getD i []))) {i : ℕ}
    (hi : i < D.xWs.length) (hent : entryOK D i (D.es.getD i default) = true) :
    MovesCentre ↥G S (Subgroup.closure ({wv D.zW, wv (D.xWs.getD i [])} : Set ↥G)) ∨
      TransitiveOn ↥G (Subgroup.closure ({wv D.zW, wv (D.xWs.getD i [])} : Set ↥G)) := by
  set e : Entry := D.es.getD i default with he
  set z : ↥G := wv D.zW with hzdef
  set x : ↥G := wv (D.xWs.getD i []) with hxdef
  have hzt : TabRep (zT D) (z : Equiv.Perm (Fin D.n)) := hwT _
  have hxt : TabRep (xT D i) (x : Equiv.Perm (Fin D.n)) := hwT _
  have hz3 : z ^ 3 = 1 := hc.z_pow
  have hx3 : x ^ 3 = 1 := hc.x_pow i hi
  have hxz : x * z = z * x := hc.x_comm i hi
  obtain ⟨hEe, hEc⟩ := closure_pair_facts hz3 hx3 hc.z_ne hxz (hc.x_not i hi)
  set E : Subgroup ↥G := Subgroup.closure ({z, x} : Set ↥G) with hE
  have hzE : z ∈ E := Subgroup.subset_closure (by simp)
  have hxE : x ∈ E := Subgroup.subset_closure (by simp)
  have hE1 : 1 ≤ Open.pRank 3 E := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h2 : 2 ≤ Open.pRank 3 E := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEe hEc
    omega
  set S' : List ↥G := e.gWs.map wv with hS'
  have hgT : ∀ j, TabRep ((gT D e).getD j (idTab D.n))
      ((S'.getD j 1 : ↥G) : Equiv.Perm (Fin D.n)) := rep_mapK (wT D) wv hwT e.gWs
  have hsize : (gT D e).size = e.gWs.length := by simp [gT]
  have hS'len : S'.length = e.gWs.length := by simp [hS']
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hent
  obtain ⟨⟨hgood, hndlen⟩, hmain⟩ := hent
  have hgTi := rep_invK (gT D e) S' hgT (by rw [hsize, hS'len]) fun j hj => (hgood j hj).1
  have hgT' : ∀ j (hj : j < e.gWs.length),
      TabRep (gT D e)[j]! ((S'.getD j 1 : ↥G) : Equiv.Perm (Fin D.n)) := by
    intro j hj
    have := hgT j
    rwa [show (gT D e).getD j (idTab D.n) = (gT D e)[j]! by simp [gT, hj]] at this
  have hspec : ∀ j (hj : j < e.gWs.length), ((e.nd.getD j default).two = true →
      S'.getD j 1 * z = (z ^ (e.nd.getD j default).α * x ^ (e.nd.getD j default).β) *
          S'.getD j 1 ∧
        S'.getD j 1 * x = (z ^ (e.nd.getD j default).γ * x ^ (e.nd.getD j default).δ) *
          S'.getD j 1) ∧
      ((e.nd.getD j default).two = false →
        z ^ (e.nd.getD j default).a * x ^ (e.nd.getD j default).b ≠ 1 ∧
          S'.getD j 1 * (z ^ (e.nd.getD j default).a * x ^ (e.nd.getD j default).b) =
            (z ^ (e.nd.getD j default).a * x ^ (e.nd.getD j default).b) ^
              (e.nd.getD j default).α * S'.getD j 1) := fun j hj =>
    nrm_spec hzt hxt (hgT' j hj) (hgood j (by rw [hsize]; exact hj)).2
  have hmemS' : ∀ g ∈ S', ∃ j, ∃ hj : j < e.gWs.length, g = S'.getD j 1 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact ⟨j, by rwa [← hS'len], by simp [List.getD_eq_getElem?_getD, hj]⟩
  have hglb : ∀ g ∈ S', g ∈ GLBCore 3 1 E := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := hmemS' g hg
    obtain ⟨hsp1, hsp2⟩ := hspec j hj
    cases hf : (e.nd.getD j default).two
    · obtain ⟨hu1, hgu⟩ := hsp2 hf
      have huE : z ^ (e.nd.getD j default).a * x ^ (e.nd.getD j default).b ∈ E :=
        Subgroup.mul_mem _ (Subgroup.pow_mem _ hzE _) (Subgroup.pow_mem _ hxE _)
      exact mem_glbCore_of_zpowers huE hu1 (hEe.2 _ huE) hgu
    · obtain ⟨h1, h2⟩ := hsp1 hf
      exact mem_glbCore_of_normalizer hE1 (mem_normalizer_closure_pair h1 h2)
  by_cases hmove : e.move = true
  · left
    rw [if_pos hmove] at hmain
    simp only [moveOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] at hmain
    obtain ⟨⟨⟨⟨hsz, hinv⟩, hne⟩, hpow⟩, hm3⟩ := hmain
    set hK : ↥G := wordVal S' e.hW with hhK
    have hhrep : TabRep (wordT D.n (gT D e) (gTi D e) e.hW)
        (hK : Equiv.Perm (Fin D.n)) := wordT_repK S' (gT D e) (gTi D e) hgT hgTi e.hW
    have hirep := tabRep_inv hhrep hsz hinv
    have hcrep := tabRep_mul hzt (tabRep_mul (tabRep_mul hhrep hzt) hirep)
    exact movesCentre_of hc.z_mem hc.z_ne hc.z_comm hc.z_gen
      (wordVal_mem S' (GLBCore 3 1 E) hglb e.hW)
      (fun h' => hne ((tabRep_eq_iff hcrep tabRep_one).2 h'))
      ((tabRep_eq_iff (tabRep_pow hcrep e.m) tabRep_one).1 hpow)
      (fun h' => hm3 (Nat.mod_eq_zero_of_dvd h'))
  · right
    rw [if_neg hmove] at hmain
    simp only [transOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, List.all_eq_true,
      Bool.or_eq_true] at hmain
    obtain ⟨⟨hall, -⟩, hwords⟩ := hmain
    have hnorm : ∀ g ∈ S', g ∈ Subgroup.normalizer (E : Set ↥G) := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := hmemS' g hg
      have hjnd : j < e.nd.length := by rw [hndlen]; exact hj
      have hmem : e.nd.getD j default ∈ e.nd := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjnd]
        exact List.getElem_mem hjnd
      obtain ⟨h1, h2⟩ := (hspec j hj).1 (hall _ hmem)
      exact mem_normalizer_closure_pair h1 h2
    refine transitiveOn_of hz3 hx3 hxz.symm hnorm (fun k => e.tWs.getD k []) ?_
    intro k hk0 hk9
    have hw := hwords k hk9
    rcases hw with hw | hw
    · omega
    · have hrep := wordT_repK S' (gT D e) (gTi D e) hgT hgTi (e.tWs.getD k [])
      exact (tabRep_eq_iff (tabRep_mul hrep hzt) (tabRep_mul
        (tabRep_mul (tabRep_pow hzt (k / 3)) (tabRep_pow hxt (k % 3))) hrep)).1 hw

end Decode

theorem datum_of_check {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {a b : Equiv.Perm (Fin n)}
    (hG : G = Subgroup.closure {a, b}) {D : Certificates.CoreE1Perm.Data} (hn : D.n = n)
    (ha : TabRep D.aT a) (hb : TabRep D.bT b)
    (hsyl : ∀ P : Sylow 3 ↥G, Nat.card (P : Subgroup ↥G) = 27)
    (h : Certificates.CoreE1Perm.check D = true) : Datum ↥G := by
  subst hn
  simp only [check, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgens, hs⟩, hz⟩, hx⟩, hlen⟩, hent⟩ := h
  have haG : a ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hbG : b ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  set SK : List ↥G := [⟨a, haG⟩, ⟨b, hbG⟩] with hSK
  have hgs : ∀ j, TabRep ((gsT D).getD j (idTab D.n))
      ((SK.getD j 1 : ↥G) : Equiv.Perm (Fin D.n)) := by
    intro j
    match j with
    | 0 =>
      rw [show (gsT D).getD 0 (idTab D.n) = D.aT by simp [gsT]]
      exact ha
    | 1 =>
      rw [show (gsT D).getD 1 (idTab D.n) = D.bT by simp [gsT]]
      exact hb
    | j + 2 =>
      rw [show (gsT D).getD (j + 2) (idTab D.n) = idTab D.n by simp [gsT]]
      simpa [hSK] using TabRep.idTab (n := D.n)
  simp only [gensOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hgens
  have hgi := rep_invK (gsT D) SK hgs (by simp [gsT, hSK]) fun j hj =>
    hgens j (by simpa [gsT] using hj)
  have hwT : ∀ w, TabRep (wT D w) ((wordVal SK w : ↥G) : Equiv.Perm (Fin D.n)) := fun w =>
    wordT_repK SK (gsT D) (giT D) hgs hgi w
  have hcore := core_of_check (wordVal SK) hwT hs hz hx
  have hdat := hcore.datumAt fun i hi =>
    entry_sound (wordVal SK) hwT hcore hi (hent i (by rw [hlen]; exact hi))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hSP⟩ := (IsPGroup.of_card hcore.card).exists_le_sylow
  have hPS : (P : Subgroup ↥G) = Subgroup.closure {g | g ∈ D.sW.map (wordVal SK)} :=
    (Subgroup.eq_of_le_of_card_ge hSP (by rw [hsyl P, hcore.card]; norm_num)).symm
  refine datum_of_sylow P ?_
  rw [hPS]
  exact hdat

end CFSG.AGLEmbedding.CoreE1
