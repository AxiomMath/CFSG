module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.NormMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem map_conj_map (A : Subgroup H) (g h : H) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      A.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  show h * (g * x * g⁻¹) * h⁻¹ = (h * g) * x * (h * g)⁻¹
  group

theorem map_conj_one (A : Subgroup H) : A.map (MulAut.conj (1 : H)).toMonoidHom = A := by
  ext x
  simp

@[expose] def orbitSet (N₀ A : Subgroup H) : Set (Subgroup H) :=
  {B | ∃ g ∈ N₀, B = A.map (MulAut.conj g).toMonoidHom}

theorem self_mem_orbitSet (N₀ A : Subgroup H) : A ∈ orbitSet N₀ A :=
  ⟨1, N₀.one_mem, (map_conj_one A).symm⟩

theorem orbitSet_map {N₀ A B : Subgroup H} {n : H} (hn : n ∈ N₀) (hB : B ∈ orbitSet N₀ A) :
    B.map (MulAut.conj n).toMonoidHom ∈ orbitSet N₀ A := by
  obtain ⟨g, hg, rfl⟩ := hB
  exact ⟨n * g, N₀.mul_mem hn hg, map_conj_map A g n⟩

theorem orbitSet_isCompIn {R N₀ A B : Subgroup H} (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H)) (hB : B ∈ orbitSet N₀ A) :
    IsCompIn B (centralizer (R : Set H)) := by
  obtain ⟨g, hg, rfl⟩ := hB
  exact isCompIn_map_conj_of_mem_normalizer hA
    (mem_normalizer_centralizer_of_mem_normalizer (hN hg))

section Finite

variable [Finite H]

noncomputable instance orbitFintype (N₀ A : Subgroup H) : Fintype ↥(orbitSet N₀ A) :=
  Fintype.ofFinite _

noncomputable instance orbitDecEq (N₀ A : Subgroup H) : DecidableEq ↥(orbitSet N₀ A) :=
  Classical.decEq _

theorem orbit_commFamily {R N₀ A : Subgroup H} (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H)) :
    CommFamily (fun B : ↥(orbitSet N₀ A) => (B : Subgroup H)) := fun i j hij x y hx hy =>
  (orbitSet_isCompIn hA hN i.2).commute_of_ne (orbitSet_isCompIn hA hN j.2)
    (fun h => hij (Subtype.ext h)) x hx y hy

omit [Finite H] in
noncomputable def orbitRep (N₀ A : Subgroup H) (B : ↥(orbitSet N₀ A)) : H := Classical.choose B.2

omit [Finite H] in
theorem orbitRep_mem (N₀ A : Subgroup H) (B : ↥(orbitSet N₀ A)) : orbitRep N₀ A B ∈ N₀ :=
  (Classical.choose_spec B.2).1

omit [Finite H] in
theorem map_orbitRep (N₀ A : Subgroup H) (B : ↥(orbitSet N₀ A)) :
    A.map (MulAut.conj (orbitRep N₀ A B)).toMonoidHom = B :=
  ((Classical.choose_spec B.2).2).symm

omit [Finite H] in
@[expose] noncomputable def orbitMap (N₀ A : Subgroup H) (B : ↥(orbitSet N₀ A)) :
    ↥A →* ↥(B : Subgroup H) :=
  ((Subgroup.equivMapOfInjective A (MulAut.conj (orbitRep N₀ A B)).toMonoidHom
    (MulAut.conj (orbitRep N₀ A B)).injective).trans
      (MulEquiv.subgroupCongr (map_orbitRep N₀ A B))).toMonoidHom

omit [Finite H] in
theorem orbitMap_coe (N₀ A : Subgroup H) (B : ↥(orbitSet N₀ A)) (x : ↥A) :
    ((orbitMap N₀ A B x : ↥(B : Subgroup H)) : H) =
      orbitRep N₀ A B * x * (orbitRep N₀ A B)⁻¹ := rfl

omit [Finite H] in
@[expose] noncomputable def orbitSup (N₀ A : Subgroup H) : Subgroup H :=
  ⨆ B : ↥(orbitSet N₀ A), (B : Subgroup H)


omit [Finite H] in
theorem le_orbitSup {N₀ A : Subgroup H} (B : ↥(orbitSet N₀ A)) :
    (B : Subgroup H) ≤ orbitSup N₀ A :=
  le_iSup (fun B : ↥(orbitSet N₀ A) => (B : Subgroup H)) B

omit [Finite H] in
theorem orbitSup_le {N₀ A K : Subgroup H} (h : ∀ B : ↥(orbitSet N₀ A), (B : Subgroup H) ≤ K) :
    orbitSup N₀ A ≤ K :=
  iSup_le h

omit [Finite H] in
theorem map_orbitSup {N₀ A : Subgroup H} (f : H →* H) :
    (orbitSup N₀ A).map f = ⨆ B : ↥(orbitSet N₀ A), (B : Subgroup H).map f :=
  Subgroup.map_iSup _ _

omit [Finite H] in
theorem orbitSup_conj {N₀ A : Subgroup H} {n : H} (hn : n ∈ N₀) :
    (orbitSup N₀ A).map (MulAut.conj n).toMonoidHom ≤ orbitSup N₀ A := by
  rw [orbitSup, Subgroup.map_iSup]
  exact iSup_le fun B => le_iSup_of_le ⟨B.1.map (MulAut.conj n).toMonoidHom,
    orbitSet_map hn B.2⟩ le_rfl

omit [Finite H] in
theorem orbitMap_conj {N₀ A : Subgroup H}
    (hS : ∀ s ∈ N₀, A.map (MulAut.conj s).toMonoidHom = A → ∀ x ∈ A, s * x * s⁻¹ = x)
    {n : H} (hn : n ∈ N₀) (B B' : ↥(orbitSet N₀ A))
    (h : (B : Subgroup H).map (MulAut.conj n).toMonoidHom = B') (x : ↥A) :
    n * ((orbitMap N₀ A B x : ↥(B : Subgroup H)) : H) * n⁻¹ =
      ((orbitMap N₀ A B' x : ↥(B' : Subgroup H)) : H) := by
  rw [orbitMap_coe, orbitMap_coe]
  set g := orbitRep N₀ A B with hg
  set g' := orbitRep N₀ A B' with hg'
  have hsN : g'⁻¹ * (n * g) ∈ N₀ :=
    N₀.mul_mem (N₀.inv_mem (orbitRep_mem _ _ _)) (N₀.mul_mem hn (orbitRep_mem _ _ _))
  have hsA : A.map (MulAut.conj (g'⁻¹ * (n * g))).toMonoidHom = A := by
    have h1 : A.map (MulAut.conj (n * g)).toMonoidHom = B' := by
      rw [← map_conj_map A g n, hg, map_orbitRep, h]
    have h2 : A.map (MulAut.conj g').toMonoidHom = B' := map_orbitRep N₀ A B'
    calc A.map (MulAut.conj (g'⁻¹ * (n * g))).toMonoidHom
        = (A.map (MulAut.conj (n * g)).toMonoidHom).map (MulAut.conj g'⁻¹).toMonoidHom :=
          (map_conj_map A (n * g) g'⁻¹).symm
      _ = (A.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g'⁻¹).toMonoidHom := by
          rw [h1, h2]
      _ = A.map (MulAut.conj (g'⁻¹ * g')).toMonoidHom := map_conj_map A g' g'⁻¹
      _ = A := by rw [inv_mul_cancel, map_conj_one]
  have key := hS _ hsN hsA x x.2
  calc n * (g * (x : H) * g⁻¹) * n⁻¹ = (n * g) * x * (n * g)⁻¹ := by group
    _ = g' * (g'⁻¹ * (n * g) * x * (g'⁻¹ * (n * g))⁻¹) * g'⁻¹ := by group
    _ = g' * x * g'⁻¹ := by rw [key]

noncomputable def orbitNorm {R N₀ A : Subgroup H} (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H)) : ↥A →* H :=
  normHom (fun B : ↥(orbitSet N₀ A) => (B : Subgroup H)) (orbit_commFamily hA hN) (orbitMap N₀ A)

theorem orbitNorm_mem {R N₀ A : Subgroup H} (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H)) (x : ↥A) : orbitNorm hA hN x ∈ orbitSup N₀ A :=
  normHom_mem _ _ _ x

theorem orbitNorm_factor {R N₀ A : Subgroup H} (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H)) (B : ↥(orbitSet N₀ A)) (x : ↥A) :
    ∃ c ∈ centralizer ((B : Subgroup H) : Set H), c ∈ orbitSup N₀ A ∧
      orbitNorm hA hN x = c * ((orbitMap N₀ A B x : ↥(B : Subgroup H)) : H) :=
  normHom_factor (fun B : ↥(orbitSet N₀ A) => (B : Subgroup H)) (orbit_commFamily hA hN)
    (orbitMap N₀ A) B x

theorem orbitNorm_commute {R N₀ A : Subgroup H} (hA : IsCompIn A (centralizer (R : Set H)))
    (hN : N₀ ≤ normalizer (R : Set H))
    (hS : ∀ s ∈ N₀, A.map (MulAut.conj s).toMonoidHom = A → ∀ x ∈ A, s * x * s⁻¹ = x)
    [Group.IsPerfect ↥A] {n : H} (hn : n ∈ N₀) :
    ∀ d ∈ (orbitNorm hA hN).range, d * n = n * d := by
  have hperf : Group.IsPerfect ↥(orbitNorm hA hN).range := Group.IsPerfect.range _
  set D := (orbitNorm hA hN).range with hD
  set E := orbitSup N₀ A with hE
  set Z : Subgroup H := E ⊓ centralizer (E : Set H) with hZdef
  have hDE : D ≤ E := by
    rintro _ ⟨x, rfl⟩
    exact orbitNorm_mem hA hN x
  have hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' =>
    (Subgroup.mem_centralizer_iff.1 hz.2 z' hz'.1).symm
  have hZD : ∀ z ∈ Z, ∀ a ∈ D, z * a = a * z := fun z hz a ha =>
    (Subgroup.mem_centralizer_iff.1 hz.2 a (hDE ha)).symm
  refine commutes_of_commutator_mem (A := D) (Z := Z) hZ hZD ?_
  rintro _ ⟨x, rfl⟩
  set u : H := orbitNorm hA hN x with hu
  set w : H := u⁻¹ * (n * u * n⁻¹) with hw
  have huE : u ∈ E := orbitNorm_mem hA hN x
  have hu'E : n * u * n⁻¹ ∈ E := orbitSup_conj hn ⟨u, huE, rfl⟩
  have hwE : w ∈ E := E.mul_mem (E.inv_mem huE) hu'E
  have hwC : ∀ B : ↥(orbitSet N₀ A), w ∈ centralizer ((B : Subgroup H) : Set H) := by
    intro B
    let B₁ : ↥(orbitSet N₀ A) := ⟨(B : Subgroup H).map (MulAut.conj n⁻¹).toMonoidHom,
      orbitSet_map (N₀.inv_mem hn) B.2⟩
    have hB₁ : (B₁ : Subgroup H).map (MulAut.conj n).toMonoidHom = B := by
      show ((B : Subgroup H).map (MulAut.conj n⁻¹).toMonoidHom).map
        (MulAut.conj n).toMonoidHom = B
      rw [map_conj_map, mul_inv_cancel, map_conj_one]
    obtain ⟨c₁, hc₁, -, hu₁⟩ := orbitNorm_factor hA hN B₁ x
    obtain ⟨c, hc, -, hu₀⟩ := orbitNorm_factor hA hN B x
    rw [← hu] at hu₁ hu₀
    have hy := orbitMap_conj hS hn B₁ B hB₁ x
    set y₁ : H := ((orbitMap N₀ A B₁ x : ↥(B₁ : Subgroup H)) : H) with hy₁
    set y : H := ((orbitMap N₀ A B x : ↥(B : Subgroup H)) : H) with hyy
    have hyB : y ∈ (B : Subgroup H) := (orbitMap N₀ A B x).2
    have hc₁' : n * c₁ * n⁻¹ ∈ centralizer ((B : Subgroup H) : Set H) := by
      refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
      have hb₁ : n⁻¹ * b * n ∈ (B₁ : Subgroup H) := ⟨b, hb, by simp⟩
      have := Subgroup.mem_centralizer_iff.1 hc₁ _ hb₁
      calc b * (n * c₁ * n⁻¹) = n * ((n⁻¹ * b * n) * c₁) * n⁻¹ := by group
        _ = n * (c₁ * (n⁻¹ * b * n)) * n⁻¹ := by rw [this]
        _ = (n * c₁ * n⁻¹) * b := by group
    have e2 : n * u * n⁻¹ = (n * c₁ * n⁻¹) * y := by
      rw [hu₁]
      calc n * (c₁ * y₁) * n⁻¹ = (n * c₁ * n⁻¹) * (n * y₁ * n⁻¹) := by group
        _ = _ := by rw [hy]
    have hq : c⁻¹ * (n * c₁ * n⁻¹) ∈ centralizer ((B : Subgroup H) : Set H) :=
      (centralizer ((B : Subgroup H) : Set H)).mul_mem
        ((centralizer ((B : Subgroup H) : Set H)).inv_mem hc) hc₁'
    have hwq : w = c⁻¹ * (n * c₁ * n⁻¹) := by
      have hqy := Subgroup.mem_centralizer_iff.1 hq y hyB
      calc w = u⁻¹ * (n * u * n⁻¹) := rfl
        _ = (c * y)⁻¹ * ((n * c₁ * n⁻¹) * y) := by rw [e2, hu₀]
        _ = y⁻¹ * (c⁻¹ * (n * c₁ * n⁻¹)) * y := by group
        _ = y⁻¹ * (y * (c⁻¹ * (n * c₁ * n⁻¹))) := by rw [mul_assoc, ← hqy]
        _ = c⁻¹ * (n * c₁ * n⁻¹) := by group
    rw [hwq]
    exact hq
  have hwcent : w ∈ centralizer (E : Set H) := by
    have hle : E ≤ centralizer ({w} : Set H) := iSup_le fun B b hb =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hwC B) b hb)
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  have hwZ : w ∈ Z := ⟨hwE, hwcent⟩
  have hw' : n * u * n⁻¹ = u * w := by simp [hw]
  have huw : u * w⁻¹ = w⁻¹ * u :=
    Subgroup.mem_centralizer_iff.1 ((centralizer (E : Set H)).inv_mem hwcent) u huE
  have hcomm : u * n * u⁻¹ * n⁻¹ = w⁻¹ := by
    calc u * n * u⁻¹ * n⁻¹ = u * (n * u * n⁻¹)⁻¹ := by group
      _ = u * (u * w)⁻¹ := by rw [hw']
      _ = (u * w⁻¹) * u⁻¹ := by group
      _ = (w⁻¹ * u) * u⁻¹ := by rw [huw]
      _ = w⁻¹ := by group
  rw [hcomm]
  exact Z.inv_mem hwZ

end Finite

end CFSG.EvenSporadicStandard.Induction
