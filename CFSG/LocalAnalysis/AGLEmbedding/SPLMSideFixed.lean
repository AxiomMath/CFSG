module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartOne.MB3.FixedPoint

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

theorem exists_fixed_mod {K : Type} [Group K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (N : Subgroup K) (hN : ¬ p ∣ (N.subgroupOf (Subgroup.center K)).index)
    (α : MulAut K) (hαp : ∀ k : K, (α ^ p) k = k) (hαN : ∀ n ∈ N, α n ∈ N)
    (k : K) (hk : k⁻¹ * α k ∈ Subgroup.center K) :
    ∃ w : K, k⁻¹ * w ∈ Subgroup.center K ∧ w⁻¹ * α w ∈ N := by
  classical
  set Z := Subgroup.center K with hZdef
  set ZN : Subgroup Z := N.subgroupOf Z with hZNdef
  have hZcomm : ∀ a b : Z, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  have : ZN.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by rw [hZcomm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hn⟩
  have hg : ∀ ζ : Z, k⁻¹ * α (k * ζ) ∈ Z := fun ζ => by
    have h1 : k⁻¹ * α (k * ζ) = (k⁻¹ * α k) * α ζ := by rw [map_mul]; group
    rw [h1]
    exact Z.mul_mem hk (MulEquivClass.apply_mem_center α ζ.2)
  let g : Z → Z := fun ζ => ⟨k⁻¹ * α (k * ζ), hg ζ⟩
  have hgn : ∀ n : ℕ, ∀ ζ : Z, ((g^[n]) ζ : K) = k⁻¹ * (α ^ n) (k * ζ) := by
    intro n
    induction n with
    | zero => intro ζ; simp
    | succ n ih =>
      intro ζ
      rw [Function.iterate_succ_apply', pow_succ']
      show k⁻¹ * α (k * ((g^[n]) ζ : K)) = _
      rw [ih ζ, MulAut.mul_apply]
      congr 2
      group
  have hgrel : ∀ a b : Z, a⁻¹ * b ∈ ZN → (g a)⁻¹ * g b ∈ ZN := by
    intro a b hab
    rw [Subgroup.mem_subgroupOf] at hab ⊢
    have h1 : (((g a)⁻¹ * g b : Z) : K) = α ((a : K)⁻¹ * b) := by
      show (k⁻¹ * α (k * a))⁻¹ * (k⁻¹ * α (k * b)) = _
      rw [map_mul, map_mul, map_mul, map_inv]
      group
    rw [h1]
    exact hαN _ (by simpa using hab)
  let f : Function.End (Z ⧸ ZN) :=
    Quotient.map' g (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hgrel a b hab)
  have hfn : ∀ n : ℕ, ∀ ζ : Z, (f ^ n) (ζ : Z ⧸ ZN) = ((g^[n]) ζ : Z ⧸ ZN) := by
    intro n
    induction n with
    | zero => intro ζ; rfl
    | succ n ih =>
      intro ζ
      rw [pow_succ', Function.iterate_succ_apply']
      show f ((f ^ n) (ζ : Z ⧸ ZN)) = _
      rw [ih ζ]
      rfl
  have hfp : f ^ p ^ 1 = 1 := by
    funext x
    obtain ⟨ζ, rfl⟩ := QuotientGroup.mk_surjective x
    rw [pow_one, hfn]
    have : (g^[p]) ζ = ζ := Subtype.ext (by
      rw [hgn, hαp]
      group)
    rw [this]
    rfl
  have : Fintype (Z ⧸ ZN) := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) hfp
  have hcard : Fintype.card (Z ⧸ ZN) = ZN.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  by_contra hnone
  have hfix0 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => hnone ?_⟩
    obtain ⟨ζ, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨k * ζ, by simp, ?_⟩
    have hx' : f (ζ : Z ⧸ ZN) = (ζ : Z ⧸ ZN) := hx
    have h1 : (g ζ : Z ⧸ ZN) = (ζ : Z ⧸ ZN) := hx'
    rw [QuotientGroup.eq] at h1
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (((g ζ)⁻¹ * ζ : Z) : K) = ((k * ζ)⁻¹ * α (k * ζ))⁻¹ := by
      show (k⁻¹ * α (k * ζ))⁻¹ * ζ = _
      group
    rw [h2] at h1
    simpa using N.inv_mem h1
  rw [hfix0, hcard] at hmod
  exact hN ((Nat.modEq_zero_iff_dvd).mp hmod)

variable {G : Type} [Group G] [Finite G]

theorem exists_noncentral_mod {p : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {c : G}
    (hK : CFSG.IsQuasisimple K) (hc : c ∈ Subgroup.normalizer (K : Set G)) (hcp : c ^ p = 1)
    (N : Subgroup K) (hN : ¬ p ∣ (N.subgroupOf (Subgroup.center K)).index)
    (hcN : ∀ n ∈ N, (⟨c * (n : G) * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc n).mp n.2⟩ : K) ∈ N) :
    ∃ k : K, k ∉ Subgroup.center K ∧ k⁻¹ * ⟨c * (k : G) * c⁻¹,
      (Subgroup.mem_normalizer_iff.mp hc k).mp k.2⟩ ∈ N := by
  by_contra hno
  push Not at hno
  obtain ⟨-, hsimple, a, b, hab⟩ := hK
  let α : MulAut K := K.normalizerMonoidHom ⟨c, hc⟩
  have hα : ∀ k : K, ((α k : K) : G) = c * k * c⁻¹ := fun k => rfl
  have hαp : α ^ p = 1 := by
    rw [← map_pow]
    have : (⟨c, hc⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := Subtype.ext hcp
    rw [this, map_one]
  have hαk : ∀ k : K, α k = ⟨c * (k : G) * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc k).mp k.2⟩ :=
    fun k => Subtype.ext (hα k)
  let ᾱ : MulAut (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) α (Subgroup.map_center_eq α)
  have hᾱ : ∀ k : K, ᾱ (k : K ⧸ Subgroup.center K) = ((α k : K) : K ⧸ Subgroup.center K) :=
    fun k => QuotientGroup.congr_mk _ _ α _ k
  have hᾱn : ∀ n : ℕ, ∀ k : K, (ᾱ ^ n) (k : K ⧸ Subgroup.center K) =
      (((α ^ n) k : K) : K ⧸ Subgroup.center K) := by
    intro n
    induction n with
    | zero => intro k; rfl
    | succ n ih =>
      intro k
      rw [pow_succ, pow_succ]
      show (ᾱ ^ n) (ᾱ k) = _
      rw [hᾱ k]
      exact ih (α k)
  have hfix : ∀ x : K ⧸ Subgroup.center K, ᾱ x = x → x = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hᾱ k, QuotientGroup.eq] at hx
    have hx' : k⁻¹ * α k ∈ Subgroup.center K := by
      have := Subgroup.inv_mem _ hx
      simpa using this
    have hNα : ∀ n ∈ N, α n ∈ N := fun n hn => by rw [hαk]; exact hcN n hn
    obtain ⟨w, hw, hαw⟩ := exists_fixed_mod N hN α (fun k => by rw [hαp]; rfl) hNα k hx'
    rw [hαk] at hαw
    have hw1 : w ∈ Subgroup.center K := by
      by_contra hwc
      exact hno w hwc hαw
    have h3 : (w : K ⧸ Subgroup.center K) = 1 := (QuotientGroup.eq_one_iff w).mpr hw1
    have h2 : ((k : K ⧸ Subgroup.center K)) = (w : K ⧸ Subgroup.center K) :=
      (QuotientGroup.eq).mpr hw
    rw [h2]
    exact h3
  have hne : ᾱ ≠ 1 := by
    intro h1
    apply hab
    have ha : a = 1 := hfix a (by rw [h1]; rfl)
    rw [ha]
    simp
  have hαp' : ᾱ ^ p = 1 := by
    ext x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hᾱn p k, hαp]
    rfl
  have hord : (orderOf ᾱ).Prime := by
    have hdvd : orderOf ᾱ ∣ p := orderOf_dvd_of_pow_eq_one hαp'
    rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · rw [h]
      exact hp.out
  have hnil := CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime ᾱ hord hfix
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hsimple
  have hle := Group.nilpotencyClass_le_one_of_isSimple_of_isNilpotent (G := K ⧸ Subgroup.center K)
  have hcomm := (Group.IsNilpotent.nilpotencyClass_le_one_iff).mp hle
  exact hab (hcomm.is_comm.comm a b)

end CFSG.AGLEmbedding.SPLMSide
