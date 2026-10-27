module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnLift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open scoped commutatorElement

section Lift

variable {M S : Type} [Group M] [Finite M] [Group S] {π : M →* S} {α : MulAut M} {β : MulAut S}

theorem commutator_mem_fix (hZc : π.ker ≤ Subgroup.center M) (hαβ : ∀ u, π (α u) = β (π u))
    {x y : M} (hx : x ∈ coverX π β) (hy : y ∈ coverX π β) : ⁅x, y⁆ ∈ u4Fix α := by
  let x' : ↥(coverX π β) := ⟨x, hx⟩
  let y' : ↥(coverX π β) := ⟨y, hy⟩
  have h1 : coverZeta hZc hαβ ⁅x', y'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.1 (hZc (coverZeta_mem_ker hZc hαβ y')) _
  have h2 : α ⁅x, y⁆ * ⁅x, y⁆⁻¹ = 1 := h1
  exact mul_inv_eq_one.1 h2

theorem perfect_le_fix (hZc : π.ker ≤ Subgroup.center M) (hαβ : ∀ u, π (α u) = β (π u))
    {L : Subgroup M} (hLX : L ≤ coverX π β) (hperf : ⁅L, L⁆ = L) : L ≤ u4Fix α := by
  calc L = ⁅L, L⁆ := hperf.symm
    _ ≤ u4Fix α := Subgroup.commutator_le.2 fun x hx y hy =>
      commutator_mem_fix hZc hαβ (hLX hx) (hLX hy)

theorem exists_perfect_lift (hπ : Function.Surjective π) (hZc : π.ker ≤ Subgroup.center M)
    (hαβ : ∀ u, π (α u) = β (π u)) (P : Subgroup S) (hP : ∀ x ∈ P, β x = x)
    {Tq : Type} [Group Tq] [Group.IsPerfect Tq] (f : ↥P →* Tq) (hf : Function.Surjective f) :
    ∃ L : Subgroup M, ⁅L, L⁆ = L ∧ L ≤ u4Fix α ∧ (∀ x ∈ L, π x ∈ P) ∧
      ∀ t : Tq, ∃ x ∈ L, ∃ h : π x ∈ P, f ⟨π x, h⟩ = t := by
  let P' : Subgroup M := P.comap π
  have hP'X : P' ≤ coverX π β := fun u hu => hP _ hu
  let g : ↥P' →* Tq := f.comp ((π.comp P'.subtype).codRestrict P (fun x => x.2))
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨y, hy⟩ := hf t
    obtain ⟨u, hu⟩ := hπ y.1
    refine ⟨⟨u, by show π u ∈ P; rw [hu]; exact y.2⟩, ?_⟩
    show f ⟨π u, _⟩ = t
    rw [← hy]
    congr 1
    exact Subtype.ext hu
  obtain ⟨Q, hQ, hQmap⟩ := CatB.I1431YD4.exists_perfect_cover g hg
  let L : Subgroup M := Q.map P'.subtype
  haveI := hQ
  have hLperf : Group.IsPerfect ↥L := Group.IsPerfect.map P'.subtype
  have hLP : ∀ x ∈ L, π x ∈ P := by
    rintro _ ⟨q, _, rfl⟩
    exact q.2
  have hLX : L ≤ coverX π β := fun x hx => hP _ (hLP x hx)
  have hLperf' : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hLperf
  refine ⟨L, hLperf', perfect_le_fix hZc hαβ hLX hLperf', hLP, ?_⟩
  intro t
  have ht : t ∈ Q.map g := by
    rw [hQmap]
    trivial
  obtain ⟨q, hq, hgq⟩ := ht
  exact ⟨q.1, ⟨q, hq, rfl⟩, q.2, hgq⟩

theorem preimage_le_fix (hZc : π.ker ≤ Subgroup.center M) (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1)
    (hZα : ∀ z ∈ π.ker, α z = z) (hαβ : ∀ u, π (α u) = β (π u)) (P : Subgroup S)
    (hP : ∀ x ∈ P, β x = x) {Tq : Type} [Group Tq] (f : ↥P →* Tq)
    (hcop : Nat.Coprime 3 (Nat.card f.ker)) (L : Subgroup M) (hLfix : L ≤ u4Fix α)
    (hLP : ∀ x ∈ L, π x ∈ P) (hLs : ∀ t : Tq, ∃ x ∈ L, ∃ h : π x ∈ P, f ⟨π x, h⟩ = t) :
    P.comap π ≤ u4Fix α := by
  intro x hx
  have hxP : π x ∈ P := hx
  obtain ⟨l, hl, hlP, hlf⟩ := hLs (f ⟨π x, hxP⟩)
  have hkP : π (x * l⁻¹) ∈ P := by
    rw [map_mul, map_inv]
    exact P.mul_mem hxP (P.inv_mem hlP)
  have hkker : (⟨π (x * l⁻¹), hkP⟩ : ↥P) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have : (⟨π (x * l⁻¹), hkP⟩ : ↥P) = ⟨π x, hxP⟩ * (⟨π l, hlP⟩ : ↥P)⁻¹ :=
      Subtype.ext (by simp)
    rw [this, map_mul, map_inv, hlf, mul_inv_cancel]
  set k := x * l⁻¹ with hk
  set m := Nat.card f.ker with hm
  have hkm : k ^ m ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    have h1 : (⟨⟨π k, hkP⟩, hkker⟩ : f.ker) ^ m = 1 := pow_card_eq_one'
    have h2 := congrArg (fun z : f.ker => (z : ↥P).1) h1
    simpa using h2
  have hkX : k ∈ coverX π β := hP _ hkP
  have hζ : α k * k⁻¹ ∈ π.ker := alpha_mul_inv_mem_ker hαβ hkX
  have hζc : α k * k⁻¹ ∈ Subgroup.center M := hZc hζ
  have hζ3 : (α k * k⁻¹) ^ 3 = 1 := hZ3 _ hζ
  have h1 : α (k ^ m) = k ^ m := hZα _ hkm
  have h2 : α (k ^ m) = (α k * k⁻¹) ^ m * k ^ m := by
    rw [map_pow]
    have hc : Commute (α k * k⁻¹) k := (Subgroup.mem_center_iff.1 hζc k).symm
    have : α k = (α k * k⁻¹) * k := by group
    conv_lhs => rw [this]
    rw [hc.mul_pow]
  have hz : (α k * k⁻¹) ^ m = 1 := by
    have h3 : (α k * k⁻¹) ^ m * k ^ m = k ^ m := h2.symm.trans h1
    simpa using h3
  have hone : α k * k⁻¹ = 1 := by
    have hd : orderOf (α k * k⁻¹) ∣ Nat.gcd 3 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hζ3) (orderOf_dvd_of_pow_eq_one hz)
    rw [hcop.gcd_eq_one] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  have hαk : α k = k := mul_inv_eq_one.1 hone
  have hxkl : x = k * l := by rw [hk]; group
  show α x = x
  rw [hxkl, map_mul, hαk, hLfix hl]

theorem relIndex_coprime [Finite S] (hπ : Function.Surjective π) (P : Subgroup S) {Tq : Type}
    [Group Tq] (f : ↥P →* Tq) (hf : Function.Surjective f)
    (hcop : Nat.Coprime 3 (Nat.card f.ker)) (L : Subgroup M) (hLP : ∀ x ∈ L, π x ∈ P)
    (hLs : ∀ t : Tq, ∃ x ∈ L, ∃ h : π x ∈ P, f ⟨π x, h⟩ = t) :
    Nat.Coprime 3 (((L.map π).comap π).subgroupOf (P.comap π)).index := by
  haveI : Finite Tq := Finite.of_surjective f hf
  have h1 : (((L.map π).comap π).subgroupOf (P.comap π)).index = (L.map π).relIndex P := by
    show ((L.map π).comap π).relIndex (P.comap π) = _
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hπ]
  rw [h1]
  have hLmP : L.map π ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hLP x hx
  have hmul := Subgroup.relIndex_mul_card (L.map π) P
  rw [inf_eq_left.2 hLmP] at hmul
  have hker := Subgroup.card_ker_mul_card_of_surjective hf
  let f' : ↥(L.map π) →* Tq := f.comp (Subgroup.inclusion hLmP)
  have hf' : Function.Surjective f' := by
    intro t
    obtain ⟨x, hx, h, hxf⟩ := hLs t
    exact ⟨⟨π x, Subgroup.mem_map_of_mem π hx⟩, hxf⟩
  obtain ⟨s, hs⟩ := Subgroup.card_dvd_of_surjective hf'
  have hTpos : 0 < Nat.card Tq := Nat.card_pos
  have hrel : (L.map π).relIndex P ∣ Nat.card f.ker := by
    refine ⟨s, ?_⟩
    have h3 : (L.map π).relIndex P * (Nat.card Tq * s) * 1 = Nat.card f.ker * Nat.card Tq := by
      rw [mul_one, ← hs, hmul, hker]
    have h4 : Nat.card Tq * ((L.map π).relIndex P * s) = Nat.card Tq * Nat.card f.ker := by
      calc Nat.card Tq * ((L.map π).relIndex P * s)
          = (L.map π).relIndex P * (Nat.card Tq * s) * 1 := by ring
        _ = Nat.card f.ker * Nat.card Tq := h3
        _ = Nat.card Tq * Nat.card f.ker := by ring
    exact (Nat.eq_of_mul_eq_mul_left hTpos h4).symm
  exact Nat.Coprime.coprime_dvd_right hrel hcop

end Lift

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
