module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LieType.Steinberg

open Subgroup
open scoped commutatorElement

universe u v

section Central

variable {G : Type*} [Group G]

theorem mul_mul_inv_of_mem_center {z : G} (hz : z ∈ center G) (g : G) : z * g * z⁻¹ = g := by
  rw [← mem_center_iff.1 hz g, mul_inv_cancel_right]

theorem commutatorElement_mul_mul_of_mem_center {c d : G} (hc : c ∈ center G)
    (hd : d ∈ center G) (a b : G) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hda : a * d = d * a := mem_center_iff.1 hd a
  calc ⁅c * a, d * b⁆ = c * (a * (d * b) * a⁻¹) * c⁻¹ * (d * b)⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = a * (d * b) * a⁻¹ * (d * b)⁻¹ := by rw [mul_mul_inv_of_mem_center hc]
    _ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by
        rw [← mul_assoc a d b, hda]
        group
    _ = ⁅a, b⁆ := by rw [mul_mul_inv_of_mem_center hd, commutatorElement_def]

end Central

section Pullback

variable {K : Type u} {Q : Type*} {P : Type v} [Group K] [Group Q] [Group P]

@[expose] def pullback (β : K →* Q) (η : P →* Q) : Subgroup (K × P) :=
  (β.comp (MonoidHom.fst K P)).eqLocus (η.comp (MonoidHom.snd K P))

variable {β : K →* Q} {η : P →* Q}

theorem mem_pullback {x : K × P} : x ∈ pullback β η ↔ β x.1 = η x.2 :=
  Iff.rfl

variable (β η) in
@[expose] def pullbackFst : pullback β η →* K :=
  (MonoidHom.fst K P).comp (pullback β η).subtype

theorem pullbackFst_apply (y : pullback β η) : pullbackFst β η y = (y : K × P).1 :=
  rfl

theorem pullbackFst_surjective (hη : Function.Surjective η) :
    Function.Surjective (pullbackFst β η) := by
  intro s
  obtain ⟨x, hx⟩ := hη (β s)
  exact ⟨⟨(s, x), hx.symm⟩, rfl⟩

theorem snd_mem_ker_of_mem_ker_pullbackFst {y : pullback β η}
    (hy : y ∈ (pullbackFst β η).ker) : (y : K × P).1 = 1 ∧ (y : K × P).2 ∈ η.ker := by
  have h1 : (y : K × P).1 = 1 := hy
  refine ⟨h1, ?_⟩
  rw [MonoidHom.mem_ker, ← mem_pullback.1 y.2, h1, map_one]

theorem ker_pullbackFst_le_center (hcen : η.ker ≤ center P) :
    (pullbackFst β η).ker ≤ center (pullback β η) := by
  intro y hy
  obtain ⟨h1, hc⟩ := snd_mem_ker_of_mem_ker_pullbackFst hy
  rw [mem_center_iff]
  intro z
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change (z : K × P).1 * (y : K × P).1 = (y : K × P).1 * (z : K × P).1
    rw [h1, mul_one, one_mul]
  · exact mem_center_iff.1 (hcen hc) (z : K × P).2

theorem isPGroup_ker_pullbackFst {p : ℕ} (hp : IsPGroup p η.ker) :
    IsPGroup p (pullbackFst β η).ker := by
  intro g
  obtain ⟨h1, hc⟩ := snd_mem_ker_of_mem_ker_pullbackFst g.2
  obtain ⟨k, hk⟩ := hp ⟨_, hc⟩
  refine ⟨k, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
  · change ((g : pullback β η) : K × P).1 ^ p ^ k = 1
    rw [h1, one_pow]
  · exact congrArg Subtype.val hk

end Pullback

section TwoKernel

variable {K : Type u} {Q : Type*} {P : Type v} [Group K] [Group Q] [Group P] {β : K →* Q}
  {η : P →* Q}

theorem exists_surjective_of_isPerfect [Finite K] [Finite P] [Group.IsPerfect P]
    (hsplit : ∀ (E : Type (max u v)) [Group E] [Finite E] (π : E →* K),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : K →* E, ∀ x, π (σ x) = x)
    (hβ : Function.Surjective β) (hη : Function.Surjective η) (hcen : η.ker ≤ center P)
    (h2 : IsPGroup 2 η.ker) :
    ∃ α : K →* P, (∀ s, η (α s) = β s) ∧ Function.Surjective α ∧ η.ker = β.ker.map α := by
  obtain ⟨σ, hσ⟩ := hsplit (pullback β η) (pullbackFst β η) (pullbackFst_surjective hη)
    (ker_pullbackFst_le_center hcen) (isPGroup_ker_pullbackFst h2)
  let α : K →* P := ((MonoidHom.snd K P).comp (pullback β η).subtype).comp σ
  have hα : ∀ s, η (α s) = β s := fun s => by
    have hmem := mem_pullback.1 (σ s).2
    have h1 : ((σ s : pullback β η) : K × P).1 = s := hσ s
    change η ((σ s : pullback β η) : K × P).2 = β s
    rw [← hmem, h1]
  have hdecomp : ∀ x : P, ∃ s, x * (α s)⁻¹ ∈ center P := fun x => by
    obtain ⟨s, hs⟩ := hβ (η x)
    refine ⟨s, hcen ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hs, mul_inv_cancel]
  have hsurj : Function.Surjective α := by
    have hcomm : commutator P ≤ α.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ := hdecomp x
      obtain ⟨t, ht⟩ := hdecomp y
      have e : ⁅x, y⁆ = ⁅α s, α t⁆ := by
        have h := commutatorElement_mul_mul_of_mem_center hs ht (α s) (α t)
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro x
    exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top x)
  refine ⟨α, hα, hsurj, ?_⟩
  ext c
  constructor
  · intro hc
    obtain ⟨s, rfl⟩ := hsurj c
    refine ⟨s, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [← hα]
    exact hc
  · rintro ⟨s, hs, rfl⟩
    rw [MonoidHom.mem_ker, hα]
    exact hs

theorem card_ker_dvd_of_isPerfect [Finite K] [Finite P] [Group.IsPerfect P]
    (hsplit : ∀ (E : Type (max u v)) [Group E] [Finite E] (π : E →* K),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : K →* E, ∀ x, π (σ x) = x)
    (hβ : Function.Surjective β) (hη : Function.Surjective η) (hcen : η.ker ≤ center P)
    (h2 : IsPGroup 2 η.ker) : Nat.card η.ker ∣ Nat.card β.ker := by
  obtain ⟨α, -, -, he⟩ := exists_surjective_of_isPerfect hsplit hβ hη hcen h2
  rw [he]
  exact card_map_dvd _ _

theorem isCyclic_ker_of_isPerfect [Finite K] [Finite P] [Group.IsPerfect P]
    (hsplit : ∀ (E : Type (max u v)) [Group E] [Finite E] (π : E →* K),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : K →* E, ∀ x, π (σ x) = x)
    (hβ : Function.Surjective β) (hη : Function.Surjective η) (hcen : η.ker ≤ center P)
    (h2 : IsPGroup 2 η.ker) [IsCyclic β.ker] : IsCyclic η.ker := by
  obtain ⟨α, -, -, he⟩ := exists_surjective_of_isPerfect hsplit hβ hη hcen h2
  rw [he]
  exact isCyclic_of_surjective (α.subgroupMap β.ker) (α.subgroupMap_surjective β.ker)

end TwoKernel

section OddPart

variable {P : Type*} [Group P]

@[expose] def oddPart (C : Subgroup P) (hC : C ≤ center P) : Subgroup P where
  carrier := {c | c ∈ C ∧ Odd (orderOf c)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨C.mul_mem ha hb, Odd.of_dvd_nat (ha'.mul hb') ?_⟩
    exact (Commute.orderOf_mul_dvd_lcm (mem_center_iff.1 (hC hb) a)).trans (Nat.lcm_dvd_mul _ _)
  one_mem' := ⟨C.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨C.inv_mem ha, by rwa [orderOf_inv]⟩

theorem mem_oddPart {C : Subgroup P} {hC : C ≤ center P} {c : P} :
    c ∈ oddPart C hC ↔ c ∈ C ∧ Odd (orderOf c) :=
  Iff.rfl

instance oddPart_normal (C : Subgroup P) (hC : C ≤ center P) : (oddPart C hC).Normal :=
  ⟨fun _ hn g => by
    rw [mem_center_iff.1 (hC hn.1) g, mul_inv_cancel_right]
    exact hn⟩

theorem exists_pow_two_pow_mem_oddPart [Finite P] {C : Subgroup P} (hC : C ≤ center P) {c : P}
    (hc : c ∈ C) : ∃ a : ℕ, c ^ 2 ^ a ∈ oddPart C hC := by
  obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨a, C.pow_mem hc _, ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) ⟨m, hcm⟩, hcm, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem eq_one_of_odd_orderOf {g : P} (hodd : Odd (orderOf g)) {k : ℕ} (hk : orderOf g = 2 ^ k) :
    g = 1 := by
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hk

end OddPart

section TwoPart

variable {K : Type u} {Q : Type*} {P : Type v} [Group K] [Group Q] [Group P] {β : K →* Q}
  {η : P →* Q}

theorem sylow_two_of_isPerfect [Finite K] [Finite P] [Group.IsPerfect P]
    (hsplit : ∀ (E : Type (max u v)) [Group E] [Finite E] (π : E →* K),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : K →* E, ∀ x, π (σ x) = x)
    (hβ : Function.Surjective β) (hη : Function.Surjective η) (hcen : η.ker ≤ center P)
    (S : Sylow 2 η.ker) :
    Nat.card S ∣ Nat.card β.ker ∧ (IsCyclic β.ker → IsCyclic S) := by
  set N := oddPart η.ker hcen
  have hN : N ≤ η.ker := fun _ hc => hc.1
  set η' : P ⧸ N →* Q := QuotientGroup.lift N η hN
  have hη' : Function.Surjective η' := by
    intro q
    obtain ⟨x, rfl⟩ := hη q
    exact ⟨x, rfl⟩
  have hker' : η'.ker = η.ker.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N η hN
  have hcen' : η'.ker ≤ center (P ⧸ N) := by
    rw [hker']
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact congrArg (QuotientGroup.mk (s := N)) (mem_center_iff.1 (hcen hc) g)
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨x, hx⟩
    rw [hker'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_pow_two_pow_mem_oddPart hcen hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  obtain ⟨α, -, -, he⟩ := exists_surjective_of_isPerfect hsplit hβ hη' hcen' h2'
  let f : S →* P ⧸ N :=
    (QuotientGroup.mk' N).comp (η.ker.subtype.comp (S : Subgroup η.ker).subtype)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsN : ((s : η.ker) : P) ∈ N := (QuotientGroup.eq_one_iff _).1 hs
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') s
    have hk' : orderOf ((s : η.ker) : P) = 2 ^ k := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hk]
    exact Subtype.ext (Subtype.ext (eq_one_of_odd_orderOf hsN.2 hk'))
  have hrange : ∀ s, f s ∈ β.ker.map α := fun s => by
    rw [← he, hker']
    exact ⟨_, (s : η.ker).2, rfl⟩
  let f' : S →* β.ker.map α := f.codRestrict _ hrange
  have hf' : Function.Injective f' := fun s t h => hf (congrArg Subtype.val h)
  refine ⟨?_, fun hZ => ?_⟩
  · have hcard : Nat.card S = Nat.card f'.range :=
      Nat.card_congr (MonoidHom.ofInjective hf').toEquiv
    rw [hcard]
    exact (card_subgroup_dvd_card f'.range).trans (card_map_dvd _ _)
  · have := isCyclic_of_surjective (α.subgroupMap β.ker) (α.subgroupMap_surjective β.ker)
    exact isCyclic_of_injective f' hf'

end TwoPart

end CFSG.LieType.Steinberg
