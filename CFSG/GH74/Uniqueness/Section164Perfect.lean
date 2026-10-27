module

public import CFSG.GH74.Uniqueness.Section4CoverRigid

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec164

theorem perf_mul_self_mem_commutator {E : Type*} [Group E]
    (hgen : closure {x : E | x * x = 1} = ⊤) (g : E) : g * g ∈ commutator E := by
  let φ : E →* Abelianization E := (powMonoidHom 2).comp Abelianization.of
  have hφ : ∀ g, φ g = Abelianization.of (g * g) := fun g => by simp [φ, sq]
  have hker : closure {x : E | x * x = 1} ≤ φ.ker := by
    refine (closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ, show x * x = 1 from hx, map_one]
  have h1 : φ g = 1 := MonoidHom.mem_ker.mp (hker (by rw [hgen]; exact mem_top g))
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, ← hφ]
  exact h1

theorem commutator_eq_top_of_odd_center
    {E : Type} [Group E] [Finite E] {n i e : ℕ}
    (hgen : closure {x : E | x * x = 1} = ⊤) (hodd : Odd (Nat.card (center E)))
    (h : Bender.BenderType (E ⧸ center E) n i e) : commutator E = ⊤ := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup (E ⧸ center E) :=
    Bender.isBenderGroup_iff_exists_benderType.mpr ⟨n, i, e, h⟩
  have hquot : commutator (E ⧸ center E) = ⊤ := commutator_eq_top_of_isBenderGroup hB
  have hsurj : Function.Surjective (QuotientGroup.mk' (center E)) :=
    QuotientGroup.mk'_surjective (center E)
  have hmap : (commutator E).map (QuotientGroup.mk' (center E)) = ⊤ := by
    rw [commutator_def, map_commutator, map_top_of_surjective _ hsurj, ← commutator_def, hquot]
  rw [eq_top_iff]
  intro g _
  have hg : (QuotientGroup.mk' (center E) g) ∈ (commutator E).map (QuotientGroup.mk' (center E)) :=
    hmap ▸ mem_top _
  obtain ⟨c, hc, hcg⟩ := hg
  have hzc : c⁻¹ * g ∈ center E := QuotientGroup.eq.mp hcg
  have hzz : (c⁻¹ * g) * (c⁻¹ * g) ∈ commutator E := by
    have hn : (commutator E).Normal := inferInstance
    have h1 : g * c⁻¹ * g⁻¹ ∈ commutator E := hn.conj_mem _ (inv_mem hc) g
    have e : (c⁻¹ * g) * (c⁻¹ * g) = c⁻¹ * (g * c⁻¹ * g⁻¹) * (g * g) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hc) h1) (perf_mul_self_mem_commutator hgen g)
  have hodd' : Odd (orderOf (c⁻¹ * g)) := by
    have hdvd : orderOf (⟨c⁻¹ * g, hzc⟩ : center E) ∣ Nat.card (center E) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨k, hk⟩ := hodd'
  have hz : c⁻¹ * g = ((c⁻¹ * g) * (c⁻¹ * g)) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf (c⁻¹ * g) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hzC : c⁻¹ * g ∈ commutator E := by
    rw [hz]
    exact pow_mem hzz _
  have e : g = c * (c⁻¹ * g) := by group
  rw [e]
  exact mul_mem hc hzC

theorem exists_conj_of_fix_sylow
    {J : Type} [Group J] [Finite J] {n i e : ℕ}
    (hperf : commutator J = ⊤) (hodd : Odd (Nat.card (center J)))
    (h : Bender.BenderType (J ⧸ center J) n i e) (S : Sylow 2 J) (σ : MulAut J)
    (hσ : ∀ s ∈ (S : Subgroup J), σ s = s) :
    ∃ r ∈ (S : Subgroup J), r * r = 1 ∧ ∀ x : J, σ x = r * x * r⁻¹ := by
  let N := center J
  let q : J →* J ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let Sb : Sylow 2 (J ⧸ N) := S.mapSurjective hq
  have hσN : N.map (σ : J →* J) = N :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance σ
  let α : MulAut (J ⧸ N) := QuotientGroup.congr N N σ hσN
  have hα : ∀ x : J, α (q x) = q (σ x) := fun x => rfl
  have hfix : ∀ x ∈ (Sb : Subgroup (J ⧸ N)), α x = x := by
    intro x hx
    have hx' : x ∈ (S : Subgroup J).map q := hx
    obtain ⟨s, hs, rfl⟩ := hx'
    rw [hα, hσ s hs]
  obtain ⟨rb, hrb, hαr⟩ := h.lemma_3_6_a Sb α hfix
  obtain ⟨r, hrS, hrq⟩ : ∃ r ∈ (S : Subgroup J), q r = rb := by
    have : rb ∈ (S : Subgroup J).map q := (Bender.mem_rootCenter_iff.mp hrb).1
    obtain ⟨r, hr, h⟩ := this
    exact ⟨r, hr, h⟩
  let τ : MulAut J := MulAut.conj r⁻¹ * σ
  have hτx : ∀ x : J, τ x = r⁻¹ * σ x * r := fun x => by
    simp [τ]
  have hτ : ∀ x : J, x⁻¹ * τ x ∈ N := by
    intro x
    have h1 : q (τ x) = q x := by
      rw [hτx, map_mul, map_mul, map_inv, hrq, ← hα x, hαr (q x)]
      group
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (q x)⁻¹ * q (τ x) = 1
    rw [h1, inv_mul_cancel]
  have hτ1 : τ = 1 := mulAut_eq_one_of_central_quotient hperf le_rfl τ hτ
  have hσr : ∀ x : J, σ x = r * x * r⁻¹ := by
    intro x
    have h := hτx x
    rw [hτ1, MulAut.one_apply] at h
    calc σ x = r * (r⁻¹ * σ x * r) * r⁻¹ := by group
      _ = r * x * r⁻¹ := by rw [← h]
  refine ⟨r, hrS, ?_, hσr⟩
  have hrb2 : rb * rb = 1 := by
    obtain ⟨t, hc⟩ := h.exists_benderCore Sb
    exact hc.center_sq rb hrb
  have hr2N : r * r ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change q (r * r) = 1
    rw [map_mul, hrq, hrb2]
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨r, hrS⟩
  have hk' : r ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd2 : orderOf (r * r) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hk', one_pow]
  have hdvdN : orderOf (r * r) ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨r * r, hr2N⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (orderOf (r * r)) (2 ^ k) := by
    have hoddo : Odd (orderOf (r * r)) := Odd.of_dvd_nat hodd hdvdN
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hoddo)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd2)

theorem exists_conj_of_centralizes_sylow
    {X : Type} [Group X] [Finite X] {F P : Subgroup X}
    {n i e : ℕ} (hgen : closure {x : X | x ∈ F ∧ x * x = 1} = F)
    (hodd : Odd (Nat.card (center ↥F))) (h : Bender.BenderType (↥F ⧸ center ↥F) n i e)
    (hP : ABGLocalTools.IsSylowOf 2 P F) {x : X} (hxF : x ∈ normalizer (F : Set X))
    (hxP : ∀ p ∈ P, x * p = p * x) :
    ∃ r ∈ P, r * r = 1 ∧ ∀ f ∈ F, x * f * x⁻¹ = r * f * r⁻¹ := by
  obtain ⟨S, rfl⟩ := hP
  have hgen' : closure {y : ↥F | y * y = 1} = ⊤ := by
    apply map_injective F.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype]
    convert hgen using 2
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val (show y * y = 1 from hy)⟩
    · rintro ⟨hyF, hy⟩
      exact ⟨⟨y, hyF⟩, Subtype.ext hy, rfl⟩
  have hperf := commutator_eq_top_of_odd_center hgen' hodd h
  have hx' : x⁻¹ ∈ normalizer (F : Set X) := inv_mem hxF
  let σ : MulAut ↥F :=
    { toFun := fun f => ⟨x * f * x⁻¹, (mem_normalizer_iff.mp hxF f).mp f.2⟩
      invFun := fun f => ⟨x⁻¹ * f * x, by
        have := (mem_normalizer_iff.mp hx' f).mp f.2
        simpa using this⟩
      left_inv := fun f => Subtype.ext (by simp [mul_assoc])
      right_inv := fun f => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun f g => Subtype.ext (by
        change x * ((f : X) * g) * x⁻¹ = (x * f * x⁻¹) * (x * g * x⁻¹)
        group) }
  have hσ : ∀ s ∈ (S : Subgroup ↥F), σ s = s := by
    intro s hs
    apply Subtype.ext
    change x * (s : X) * x⁻¹ = s
    rw [hxP s ⟨s, hs, rfl⟩]
    group
  obtain ⟨r, hrS, hr2, hσr⟩ := exists_conj_of_fix_sylow hperf hodd h S σ hσ
  refine ⟨r, ⟨r, hrS, rfl⟩, congrArg Subtype.val hr2, fun f hf => ?_⟩
  have h1 := congrArg Subtype.val (hσr ⟨f, hf⟩)
  have h2 : ((σ ⟨f, hf⟩ : ↥F) : X) = x * f * x⁻¹ := rfl
  rw [h2] at h1
  simpa using h1

end Sec164

end CFSG.GH74.Uniqueness
