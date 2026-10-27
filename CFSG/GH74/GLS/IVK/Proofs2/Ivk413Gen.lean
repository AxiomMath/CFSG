module

public import CFSG.GH74.GLS.Stage2.Final.ModelComps
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.Ivk413

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.GLS.IVK.GHInv CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

section Basic

variable {H : Type} [Group H] (K : Subgroup H)

theorem centralizer_inf_subgroupOf {z : H} (hz : z ∈ K) :
    (centralizer ({z} : Set H) ⊓ K).subgroupOf K = centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K) := by
  ext ⟨x, hx⟩
  simp only [mem_subgroupOf, mem_inf, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨h, -⟩
    exact Subtype.ext h
  · intro h
    exact ⟨congrArg Subtype.val h, hx⟩

theorem centralizer_inf_eq_map {z : H} (hz : z ∈ K) :
    centralizer ({z} : Set H) ⊓ K = (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)).map K.subtype := by
  rw [← centralizer_inf_subgroupOf K hz, map_subgroupOf_eq_of_le inf_le_right]

@[expose] noncomputable def eqCK {z : H} (hz : z ∈ K) :
    ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) ≃* ↥(centralizer ({z} : Set H) ⊓ K) :=
  (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr (centralizer_inf_eq_map K hz).symm)

theorem layer_map_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem layer_centralizer_inf {z : H} (hz : z ∈ K) :
    (layer ↥(centralizer ({z} : Set H) ⊓ K)).map (centralizer ({z} : Set H) ⊓ K).subtype =
      (IVK.Ez (⟨z, hz⟩ : ↥K)).map K.subtype := by
  have h := layer_map_mulEquiv' (eqCK K hz)
  rw [← h, IVK.Ez, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem card_centralizer_inf {z : H} (hz : z ∈ K) :
    Nat.card ↥(centralizer ({z} : Set H) ⊓ K) =
      Nat.card ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) :=
  (Nat.card_congr (eqCK K hz).toEquiv).symm

theorem card_layer_centralizer_inf {z : H} (hz : z ∈ K) :
    Nat.card ↥((layer ↥(centralizer ({z} : Set H) ⊓ K)).map
        (centralizer ({z} : Set H) ⊓ K).subtype) =
      Nat.card ↥(IVK.Ez (⟨z, hz⟩ : ↥K)) := by
  rw [layer_centralizer_inf K hz, Subgroup.card_map_of_injective K.subtype_injective]

end Basic

section PCoreOf

variable {G : Type*} [Group G]

theorem pPrimeCoreOf_map_injective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (X : Subgroup A) :
    pPrimeCoreOf 2 (X.map f) = (pPrimeCoreOf 2 X).map f := by
  let e : ↥X ≃* ↥(X.map f) := Subgroup.equivMapOfInjective X f hf
  have h1 := pPrimeCore_map_iso 2 e
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_pPrimeCoreOf_of_normal_odd {X N : Subgroup G} (hNX : N ≤ X)
    (hn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnorm : (N.subgroupOf X).Normal := ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    simpa using hn g g.2 a ha⟩
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle := le_pPrimeCore_of_normal_coprime hnorm hcop
  intro n hn'
  exact ⟨⟨n, hNX hn'⟩, hle (by rw [mem_subgroupOf]; exact hn'), rfl⟩

theorem conj_mem_pPrimeCoreOf [Finite G] {X : Subgroup G} {c : G}
    (hc : ∀ x ∈ X, c * x * c⁻¹ ∈ X) (hc' : ∀ x ∈ X, c⁻¹ * x * c ∈ X) {y : G}
    (hy : y ∈ pPrimeCoreOf 2 X) : c * y * c⁻¹ ∈ pPrimeCoreOf 2 X := by
  have hle : ((pPrimeCoreOf 2 X).map (MulAut.conj c).toMonoidHom) ≤ pPrimeCoreOf 2 X := by
    refine le_pPrimeCoreOf_of_normal_odd ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hc w (pPrimeCoreOf_le X hw)
    · rintro x hx _ ⟨w, hw, rfl⟩
      have h1 : c⁻¹ * x * c ∈ X := hc' x hx
      have h2 := pPrimeCoreOf_conj h1 hw
      have : x * ((MulAut.conj c).toMonoidHom w) * x⁻¹ =
          (MulAut.conj c).toMonoidHom ((c⁻¹ * x * c) * w * (c⁻¹ * x * c)⁻¹) := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]
      exact ⟨_, h2, rfl⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact odd_card_pPrimeCoreOf X
  exact hle ⟨y, hy, rfl⟩

theorem eq_one_of_sq_eq_one_of_odd {n : G} (h : n * n = 1) (hodd : Odd (orderOf n)) : n = 1 := by
  have hdvd : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

end PCoreOf

section ShapeCore

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]

theorem sq_mem_of_sup_zpowers {J : Subgroup Y} [J.Normal] {t : Y} (ht : t * t = 1)
    (hgen : J ⊔ Subgroup.zpowers t = ⊤) (g : Y) : g * g ∈ J := by
  have hg : g ∈ J ⊔ Subgroup.zpowers t := by rw [hgen]; trivial
  rw [Subgroup.mem_sup_of_normal_left] at hg
  obtain ⟨j, hj, a, ha, rfl⟩ := hg
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  have ha' : a = 1 ∨ a = t := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left; rw [zpow_mul, ht2, one_zpow]
    · right; rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rcases ha' with h | h
  · rw [h]; simpa using J.mul_mem hj hj
  · rw [h]
    have e : j * t * (j * t) = j * (t * j * t⁻¹) := by
      rw [hti]; group
    rw [e]
    exact J.mul_mem hj (by simpa [hti] using (inferInstance : J.Normal).conj_mem j hj t)

theorem pPrimeCore_shape_eq_bot (S : Shape Y F₁ F₂)
    (hodd₁ : Odd (Nat.card F₁)) (h3₁ : 3 ≤ Nat.card F₁)
    (hodd₂ : Odd (Nat.card F₂)) (h3₂ : 3 ≤ Nat.card F₂) :
    pPrimeCore 2 Y = ⊥ := by
  have := normal_I₁ S
  have := normal_I₂ S
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.1 hcop
  have hord : ∀ n ∈ N, Odd (orderOf n) := fun n hn =>
    Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn)
  have hbot : ∀ (I : Subgroup Y) [I.Normal] {F : Type} [Field F] [Finite F]
      (e : ↥I ≃* SL(2, F)), Odd (Nat.card F) → 3 ≤ Nat.card F → N ⊓ I = ⊥ := by
    intro I _ F _ _ e hodd h3
    have hnormI : ((N ⊓ I).subgroupOf I).Normal := ⟨fun a ha g => by
      rw [mem_subgroupOf, mem_inf] at ha ⊢
      exact ⟨by simpa using hN.conj_mem _ ha.1 g,
        by simpa using I.mul_mem (I.mul_mem g.2 ha.2) (I.inv_mem g.2)⟩⟩
    have hoddI : Odd (Nat.card ((N ⊓ I).subgroupOf I)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ I ≤ I)).toEquiv]
      exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_left)
    have := CFSG.ClassicalInvolution.normal_odd_of_equiv_sl2 hodd h3 e _ hnormI hoddI
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥I) ∈ (N ⊓ I).subgroupOf I := hx
    rw [this, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  have h1 := hbot S.I₁ S.e₁ hodd₁ h3₁
  have h2 := hbot S.I₂ S.e₂ hodd₂ h3₂
  have hcomm : ∀ (I : Subgroup Y) [I.Normal], N ⊓ I = ⊥ → ∀ n ∈ N, ∀ a ∈ I, n * a = a * n := by
    intro I _ hI n hn a ha
    have hmem : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ I := by
      refine ⟨?_, ?_⟩
      · have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
        rw [e]
        exact N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) a)
      · exact I.mul_mem (Subgroup.Normal.conj_mem inferInstance a ha n) (I.inv_mem ha)
    rw [hI, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm (g₁ := n) (g₂ := a)).1
      (by simpa [commutatorElement_def] using hmem)
  have hJ : ∀ n ∈ N, n ∈ S.I₁ ⊔ S.I₂ := by
    intro n hn
    obtain ⟨k, hk⟩ := hord n hn
    have hsq := sq_mem_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) S.t_sq S.gen n
    have h1 : n ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one n
    have e : n = (n * n) ^ (k + 1) := by
      have : (n * n) ^ (k + 1) = n ^ (2 * k + 1) * n := by
        rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
      rw [this, h1, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ hsq _
  have hz2 : ∀ (I : Subgroup Y) {F : Type} [Field F] [Finite F] (e : ↥I ≃* SL(2, F)),
      Odd (Nat.card F) → ∀ a ∈ I, (∀ c ∈ I, a * c = c * a) → a * a = 1 := by
    intro I F _ _ e hodd a ha hac
    have hz : (⟨a, ha⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hac g g.2).symm
    have hcard := CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥I)) (x := ⟨⟨a, ha⟩, hz⟩)
    rw [hcard] at h
    have h' : (⟨a, ha⟩ : ↥I) ^ 2 = 1 := congrArg Subtype.val h
    have h'' : a ^ 2 = 1 := congrArg Subtype.val h'
    simpa [sq] using h''
  apply eq_bot_iff.2
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left (s := S.I₁)).1 (hJ n hn)
  have hn1 := hcomm S.I₁ h1 n hn
  have hn2 := hcomm S.I₂ h2 n hn
  have ha1 : ∀ c ∈ S.I₁, a * c = c * a := by
    intro c hc
    have h := hn1 c hc
    rw [← hab] at h
    have e1 : a * b * c = a * c * b := by
      rw [mul_assoc, ← S.comm c hc b hb, ← mul_assoc]
    have e2 : c * (a * b) = c * a * b := by rw [mul_assoc]
    rw [e1, e2] at h
    exact mul_right_cancel h
  have hb2 : ∀ c ∈ S.I₂, b * c = c * b := by
    intro c hc
    have h := hn2 c hc
    rw [← hab] at h
    have e1 : a * b * c = a * (b * c) := by rw [mul_assoc]
    have e2 : c * (a * b) = a * (c * b) := by
      rw [← mul_assoc, ← S.comm a ha c hc, mul_assoc]
    rw [e1, e2] at h
    exact mul_left_cancel h
  have haa := hz2 S.I₁ S.e₁ hodd₁ a ha ha1
  have hbb := hz2 S.I₂ S.e₂ hodd₂ b hb hb2
  have hnn : n * n = 1 := by
    rw [← hab]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← S.comm a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  exact eq_one_of_sq_eq_one_of_odd hnn (hord n hn)

end ShapeCore

end CFSG.GH74.Ivk413
