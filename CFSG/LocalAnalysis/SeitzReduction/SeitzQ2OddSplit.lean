module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup
open scoped commutatorElement
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)
open CFSG.LieType.Steinberg (pullback pullbackFst pullbackFst_surjective ker_pullbackFst_le_center
  snd_mem_ker_of_mem_ker_pullbackFst mem_pullback commutatorElement_mul_mul_of_mem_center)
open CFSG.LieType.Steinberg.CentralExt.CoprimeSplit (copPart mem_copPart
  exists_pow_prime_pow_mem_copPart)

theorem charTwo_of_natCard_eq_two_pow {K : Type} [Field K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem oddSchurTrivial_of_oddCentralSplit {S : Type} [Group S] (h : OddCentralSplit S) :
    OddSchurTrivial S := by
  intro P _ _ hP η hη hcen hodd
  obtain ⟨σ, hσ⟩ := h P η hη hcen hodd
  have := hP
  exact F4Pilot.injective_of_section_of_perfect η hcen σ hσ

theorem oddCentralSplit_of_oddSchurTrivial {S : Type} [Group S] [Group.IsPerfect S]
    (h : OddSchurTrivial S) : OddCentralSplit S := by
  intro E _ _ π hπ hcen hodd
  have : Finite S := Finite.of_surjective π hπ
  set P := CFSG.Quasithin.perfectCore (⊤ : Subgroup E) with hPdef
  have hPp : Group.IsPerfect P :=
    Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
  set η : P →* S := π.comp P.subtype with hηdef
  have hmap : P.map π = ⊤ := by
    rw [hPdef, CFSG.Quasithin.map_perfectCore, Subgroup.map_top_of_surjective π hπ]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect (by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hη : Function.Surjective η := fun g => by
    have hg : g ∈ P.map π := hmap ▸ Subgroup.mem_top g
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : η.ker ≤ center P := fun x hx => by
    have hx' : (x : E) ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)
    exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx') y)
  let ι : η.ker →* π.ker :=
    { toFun := fun x => ⟨((x : P) : E), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y hxy => by
    have h := congrArg (fun z : π.ker => (z : E)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hodd' : Odd (Nat.card η.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
  have hinj : Function.Injective η := h P hPp η hη hker hodd'
  let e : P ≃* S := MulEquiv.ofBijective η ⟨hinj, hη⟩
  exact ⟨P.subtype.comp e.symm.toMonoidHom, fun g => e.apply_symm_apply g⟩

theorem oddCentralSplit_iff_oddSchurTrivial {S : Type} [Group S] [Group.IsPerfect S] :
    OddCentralSplit S ↔ OddSchurTrivial S :=
  ⟨oddSchurTrivial_of_oddCentralSplit, oddCentralSplit_of_oddSchurTrivial⟩

section Pullback

variable {S Q P : Type} [Group S] [Group Q] [Group P] {β : S →* Q} {η : P →* Q}

theorem odd_card_ker_pullbackFst (hodd : Odd (Nat.card η.ker)) :
    Odd (Nat.card (pullbackFst β η).ker) := by
  let f : (pullbackFst β η).ker →* η.ker :=
    { toFun := fun y =>
        ⟨((y : pullback β η) : S × P).2, (snd_mem_ker_of_mem_ker_pullbackFst y.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun y z hyz => by
    have h2 : ((y : pullback β η) : S × P).2 = ((z : pullback β η) : S × P).2 :=
      congrArg Subtype.val hyz
    have h1y := (snd_mem_ker_of_mem_ker_pullbackFst y.2).1
    have h1z := (snd_mem_ker_of_mem_ker_pullbackFst z.2).1
    exact Subtype.ext (Subtype.ext (Prod.ext (h1y.trans h1z.symm) h2))
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)

theorem exists_surjective_of_oddCentralSplit [Finite S] [Finite P] [Group.IsPerfect P]
    (hS : OddCentralSplit S) (hβ : Function.Surjective β) (hη : Function.Surjective η)
    (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    ∃ α : S →* P, (∀ s, η (α s) = β s) ∧ Function.Surjective α ∧ η.ker = β.ker.map α := by
  obtain ⟨σ, hσ⟩ := hS (pullback β η) (pullbackFst β η) (pullbackFst_surjective hη)
    (ker_pullbackFst_le_center hcen) (odd_card_ker_pullbackFst hodd)
  let α : S →* P := ((MonoidHom.snd S P).comp (pullback β η).subtype).comp σ
  have hα : ∀ s, η (α s) = β s := fun s => by
    have hmem := mem_pullback.1 (σ s).2
    have h1 : ((σ s : pullback β η) : S × P).1 = s := hσ s
    change η ((σ s : pullback β η) : S × P).2 = β s
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

theorem card_ker_dvd_of_oddCentralSplit [Finite S] [Finite P] [Group.IsPerfect P]
    (hS : OddCentralSplit S) (hβ : Function.Surjective β) (hη : Function.Surjective η)
    (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    Nat.card η.ker ∣ Nat.card β.ker := by
  obtain ⟨α, -, -, he⟩ := exists_surjective_of_oddCentralSplit hS hβ hη hcen hodd
  rw [he]
  exact card_map_dvd _ _

end Pullback

section Quotient

variable {S : Type} [Group S] [Finite S]

theorem oddSchurTrivial_quotient_of_isPGroup (hS : OddCentralSplit S) {N : Subgroup S} [N.Normal]
    (h2 : IsPGroup 2 N) : OddSchurTrivial (S ⧸ N) := by
  intro P _ _ hP η hη hcen hodd
  have := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, -, -, hker⟩ := exists_surjective_of_oddCentralSplit hS
    (QuotientGroup.mk'_surjective N) hη hcen hodd
  rw [QuotientGroup.ker_mk'] at hker
  have h2' : IsPGroup 2 η.ker := by
    rw [hker]
    exact h2.map α
  have hcard : Nat.card η.ker = 1 := by
    rcases h2'.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (even_iff_two_dvd.2 h) (Nat.not_even_iff_odd.2 hodd)
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem not_oddSchurTrivial_quotient_of_not_isPGroup [Group.IsPerfect S] {N : Subgroup S}
    [N.Normal] (hN : N ≤ center S) (h2 : ¬ IsPGroup 2 N) : ¬ OddSchurTrivial (S ⧸ N) := by
  intro h
  obtain ⟨p, hp, hpN, hp2⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card N ∧ p ≠ 2 := by
    by_contra hcon
    push Not at hcon
    apply h2
    have hpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun hd hdN => hcon _ hd hdN)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpN
  set T := copPart p N hN with hTdef
  have hTN : T ≤ N := fun _ h => h.1
  have hTker : T ≤ (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hTN
  set η : S ⧸ T →* S ⧸ N := QuotientGroup.lift T (QuotientGroup.mk' N) hTker with hηdef
  have hηmk : ∀ s : S, η (s : S ⧸ T) = (s : S ⧸ N) := fun s => rfl
  have hη : Function.Surjective η := fun y => by
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(s : S ⧸ T), rfl⟩
  have hmemN : ∀ s : S, (s : S ⧸ T) ∈ η.ker → s ∈ N := fun s hs => by
    rw [MonoidHom.mem_ker, hηmk, QuotientGroup.eq_one_iff] at hs
    exact hs
  have hP : Group.IsPerfect (S ⧸ T) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective T)
  have hcen : η.ker ≤ center (S ⧸ T) := fun y hy => by
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective T)
      ⟨s, hN (hmemN s hy), rfl⟩
  have hpgrp : IsPGroup p η.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := exists_pow_prime_pow_mem_copPart (p := p) hN (hmemN s hy)
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have hodd : Odd (Nat.card η.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpgrp
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hinj := h (S ⧸ T) hP η hη hcen hodd
  have hx1 : η ((x : S) : S ⧸ T) = η 1 := by
    rw [hηmk, map_one, QuotientGroup.eq_one_iff]
    exact x.2
  have hxT : (x : S) ∈ T := (QuotientGroup.eq_one_iff _).1 (hinj hx1)
  have hcop := (mem_copPart.1 hxT).2
  rw [Subgroup.orderOf_coe, hx] at hcop
  exact hp.one_lt.ne' ((Nat.coprime_self p).1 hcop)

theorem oddSchurTrivial_quotient_iff [Group.IsPerfect S] (hS : OddCentralSplit S)
    {N : Subgroup S} [N.Normal] (hN : N ≤ center S) :
    OddSchurTrivial (S ⧸ N) ↔ IsPGroup 2 N :=
  ⟨fun h => by_contra fun h2 => not_oddSchurTrivial_quotient_of_not_isPGroup hN h2 h,
    oddSchurTrivial_quotient_of_isPGroup hS⟩

theorem oddSchurTrivial_quotient_center_iff [Group.IsPerfect S] (hS : OddCentralSplit S) :
    OddSchurTrivial (S ⧸ center S) ↔ IsPGroup 2 (center S) :=
  oddSchurTrivial_quotient_iff hS le_rfl

end Quotient

end CFSG.SeitzReduction.SeitzQ2
