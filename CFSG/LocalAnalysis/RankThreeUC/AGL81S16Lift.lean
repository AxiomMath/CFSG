module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

private theorem liftAux_eq_one_of_two_pow {Y : Type*} [Group Y] {x : Y} {p m n : ℕ}
    (hcop : Nat.Coprime (2 ^ m) (p ^ n)) (h2 : x ^ 2 ^ m = 1) (hp : x ^ p ^ n = 1) :
    x = 1 := by
  have ho : orderOf x ∣ Nat.gcd (2 ^ m) (p ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hp)
  rw [Nat.Coprime.gcd_eq_one hcop] at ho
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho)

private theorem liftAux_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {A : Subgroup G} (hA : IsElemAbelian p A) (j : G →* H) :
    IsElemAbelian p (A.map j) := by
  exact CFSG.Open.IsElemAbelian.map hA j

theorem exists_elemAbelian_lift_of_ker {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (f : X →* Q) (hker : IsPGroup 2 ↥f.ker) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup Q} (hE : IsElemAbelian p E) (hEf : E ≤ f.range) :
    ∃ S : Subgroup X, IsElemAbelian p S ∧ Nat.card S = Nat.card E ∧ S.map f = E := by
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup X := E.comap f with hP
  set f' : ↥P →* ↥E := (f.comp P.subtype).codRestrict E (fun x => x.2) with hf'
  have hf's : Function.Surjective f' := by
    rintro ⟨q, hq⟩
    obtain ⟨k, rfl⟩ := hEf hq
    exact ⟨⟨k, hq⟩, rfl⟩
  have hE3 : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow p ↥P) := inferInstance
  have htop : (S₀ : Subgroup ↥P).map f' = ⊤ := by
    have hS := (S₀.mapSurjective hf's).3 (Q := ⊤) (hE3.of_equiv Subgroup.topEquiv.symm) le_top
    rw [Sylow.coe_mapSurjective] at hS
    exact hS.symm
  have hinj : ∀ s ∈ (S₀ : Subgroup ↥P), f' s = 1 → s = 1 := by
    intro s hs hs1
    have hk : (s : X) ∈ f.ker := by
      have h := congrArg Subtype.val hs1
      exact h
    obtain ⟨m, hm⟩ := hker ⟨(s : X), hk⟩
    obtain ⟨n, hn⟩ := S₀.isPGroup' ⟨s, hs⟩
    have h2 : s ^ 2 ^ m = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hm
      simpa using this
    have h3 : s ^ p ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hcop : Nat.Coprime (2 ^ m) (p ^ n) :=
      Nat.Coprime.pow m n ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    exact liftAux_eq_one_of_two_pow hcop h2 h3
  have hS₀ : IsElemAbelian p (S₀ : Subgroup ↥P) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have hc : f' (a : ↥P) * f' (b : ↥P) = f' (b : ↥P) * f' (a : ↥P) :=
        hE.1.is_comm.comm (f' (a : ↥P)) (f' (b : ↥P))
      have hs : (a : ↥P) * (b : ↥P) * ((b : ↥P) * (a : ↥P))⁻¹ = 1 := by
        apply hinj _ ((S₀ : Subgroup ↥P).mul_mem ((S₀ : Subgroup ↥P).mul_mem a.2 b.2)
          ((S₀ : Subgroup ↥P).inv_mem ((S₀ : Subgroup ↥P).mul_mem b.2 a.2)))
        rw [map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
      exact Subtype.ext (mul_inv_eq_one.mp hs)
    · have hfx : f' x ^ p = 1 := Subtype.ext (by simpa using hE.2 _ (f' x).2)
      exact hinj (x ^ p) ((S₀ : Subgroup ↥P).pow_mem hx p) (by rw [map_pow, hfx])
  refine ⟨(S₀ : Subgroup ↥P).map P.subtype, liftAux_isElemAbelian_map hS₀ P.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective P.subtype_injective]
    set g : ↥(S₀ : Subgroup ↥P) →* ↥E := f'.comp (S₀ : Subgroup ↥P).subtype with hg
    have hginj : Function.Injective g := by
      intro a b hab
      have hab' : f' (a : ↥P) = f' (b : ↥P) := hab
      have hs := hinj ((a : ↥P) * (b : ↥P)⁻¹)
        ((S₀ : Subgroup ↥P).mul_mem a.2 ((S₀ : Subgroup ↥P).inv_mem b.2))
        (by rw [map_mul, map_inv, hab', mul_inv_cancel])
      exact Subtype.ext (mul_inv_eq_one.mp hs)
    have hgsurj : Function.Surjective g := by
      intro e
      have he : e ∈ (S₀ : Subgroup ↥P).map f' := by
        rw [htop]
        exact Subgroup.mem_top e
      obtain ⟨s, hs, hsf⟩ := he
      exact ⟨⟨s, hs⟩, hsf⟩
    exact Nat.card_congr (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩).toEquiv
  · apply le_antisymm
    · rintro _ ⟨x, ⟨s, hs, rfl⟩, rfl⟩
      exact s.2
    · intro e he
      have he' : (⟨e, he⟩ : ↥E) ∈ (S₀ : Subgroup ↥P).map f' := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨s, hs, hsf⟩ := he'
      have hfs : f (s : X) = e := congrArg Subtype.val hsf
      exact ⟨(s : X), ⟨s, hs, rfl⟩, hfs⟩

end CFSG.LocalAnalysis.RankThreeUC
