module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.ThreeCycle

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G}

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private lemma add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma eq_of_add_eq_zero_V6 {u c : V6} (h : u + c = 0) : u = c := by
  calc u = u + 0 := (add_zero u).symm
    _ = u + (c + c) := by rw [add_self_eq_zero_V6]
    _ = (u + c) + c := (add_assoc u c c).symm
    _ = 0 + c := by rw [h]
    _ = c := zero_add c

@[expose] def Induces (ι : Elem2 6 →* G) (x : G) (g : Equiv.Perm V6) : Prop :=
  ∀ v : V6, x * coordElt ι v * x⁻¹ = coordElt ι (g v)

theorem induces_one : Induces ι (1 : G) 1 := fun v => by simp

theorem Induces.mul {x y : G} {g h : Equiv.Perm V6} (hx : Induces ι x g) (hy : Induces ι y h) :
    Induces ι (x * y) (g * h) := fun v => by
  have h1 : x * y * coordElt ι v * (x * y)⁻¹ = x * (y * coordElt ι v * y⁻¹) * x⁻¹ := by group
  rw [h1, hy v, hx (h v)]
  rfl

theorem Induces.inv {x : G} {g : Equiv.Perm V6} (hx : Induces ι x g) : Induces ι x⁻¹ g⁻¹ :=
  fun v => by
  have h := hx (g⁻¹ v)
  have h2 : g (g⁻¹ v) = v := by simp
  rw [h2] at h
  calc x⁻¹ * coordElt ι v * x⁻¹⁻¹ = x⁻¹ * (x * coordElt ι (g⁻¹ v) * x⁻¹) * x := by
        rw [h]; simp
    _ = coordElt ι (g⁻¹ v) := by group

theorem induces_coordElt (v : V6) : Induces ι (coordElt ι v) 1 := fun w => by
  have h : coordElt ι v * coordElt ι w = coordElt ι w * coordElt ι v := by
    rw [← coordElt_add, ← coordElt_add, add_comm]
  rw [Equiv.Perm.one_apply]
  calc coordElt ι v * coordElt ι w * (coordElt ι v)⁻¹
      = coordElt ι w * coordElt ι v * (coordElt ι v)⁻¹ := by rw [h]
    _ = coordElt ι w := by group

@[expose] def indSub (ι : Elem2 6 →* G) (Hg : Subgroup (Equiv.Perm V6)) : Subgroup G where
  carrier := {x | ∃ g ∈ Hg, Induces ι x g}
  mul_mem' := by
    rintro x y ⟨g, hg, hx⟩ ⟨h, hh, hy⟩
    exact ⟨g * h, Hg.mul_mem hg hh, hx.mul hy⟩
  one_mem' := ⟨1, Hg.one_mem, induces_one⟩
  inv_mem' := by
    rintro x ⟨g, hg, hx⟩
    exact ⟨g⁻¹, Hg.inv_mem hg, hx.inv⟩

theorem mem_indSub {Hg : Subgroup (Equiv.Perm V6)} {x : G} :
    x ∈ indSub ι Hg ↔ ∃ g ∈ Hg, Induces ι x g := Iff.rfl

theorem coordElt_mem_indSub (Hg : Subgroup (Equiv.Perm V6)) (v : V6) :
    coordElt ι v ∈ indSub ι Hg := ⟨1, Hg.one_mem, induces_coordElt v⟩

@[expose] def indGroup (ι : Elem2 6 →* G) (K : Subgroup G) : Subgroup (Equiv.Perm V6) where
  carrier := {g | ∃ x ∈ K, Induces ι x g}
  mul_mem' := by
    rintro g h ⟨x, hx, hg⟩ ⟨y, hy, hh⟩
    exact ⟨x * y, K.mul_mem hx hy, hg.mul hh⟩
  one_mem' := ⟨1, K.one_mem, induces_one⟩
  inv_mem' := by
    rintro g ⟨x, hx, hg⟩
    exact ⟨x⁻¹, K.inv_mem hx, hg.inv⟩

theorem mem_indGroup {K : Subgroup G} {g : Equiv.Perm V6} :
    g ∈ indGroup ι K ↔ ∃ x ∈ K, Induces ι x g := Iff.rfl

theorem Induces.unique (hι : Function.Injective ι) {x : G} {g g' : Equiv.Perm V6}
    (hg : Induces ι x g) (hg' : Induces ι x g') : g = g' := by
  apply Equiv.ext
  intro v
  apply coordElt_injective hι
  rw [← hg v, ← hg' v]

theorem Induces.exists_eq_coordElt (hC : centralizer (ι.range : Set G) ≤ ι.range) {x : G}
    (hx : Induces ι x 1) : ∃ v : V6, x = coordElt ι v := by
  have hxcent : x ∈ centralizer (ι.range : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    have h := hx (Multiplicative.toAdd a)
    simp only [Equiv.Perm.one_apply] at h
    have h' : x * ι a * x⁻¹ = ι a := by simpa [coordElt] using h
    exact (mul_inv_eq_iff_eq_mul.mp h').symm
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hC hxcent)
  exact ⟨Multiplicative.toAdd a, by rw [coordElt, ofAdd_toAdd, ha]⟩

theorem Induces.mem_of_mem_indSub (hι : Function.Injective ι) {Hg : Subgroup (Equiv.Perm V6)}
    {x : G} {g : Equiv.Perm V6} (hx : x ∈ indSub ι Hg) (hg : Induces ι x g) : g ∈ Hg := by
  obtain ⟨g', hg', hg'x⟩ := mem_indSub.mp hx
  rwa [Induces.unique hι hg'x hg] at hg'

@[expose] def E24 (ι : Elem2 6 →* G) (a : G) : Subgroup G :=
  ι.range ⊓ centralizer ({a} : Set G)

@[expose] def F24 (ι : Elem2 6 →* G) (a : G) : Subgroup G :=
  indSub ι A5g ⊓ centralizer ({a} : Set G)

@[expose] def P24 (ι : Elem2 6 →* G) (a : G) : Subgroup G :=
  indSub ι Vg ⊓ centralizer ({a} : Set G)

structure Setting24 (ι : Elem2 6 →* G) (a : G) : Prop where
  inj : Function.Injective ι
  centralizer_le : centralizer (ι.range : Set G) ≤ ι.range
  induced : inducedGroup ι = OmegaPlus
  a_cube : a ^ 3 = 1
  a_induces : Induces ι a w3

theorem exists_mul_comm_of_induces {a x : G} {w g : Equiv.Perm V6}
    (hι : Function.Injective ι) (hC : centralizer (ι.range : Set G) ≤ ι.range)
    (ha3 : a ^ 3 = 1) (haw : Induces ι a w) (hxg : Induces ι x g)
    (hgw : g * w = w * g) : ∃ c : V6, coordElt ι c * x * a = a * (coordElt ι c * x) := by
  have hconj : g * w * g⁻¹ = w := by rw [hgw]; group
  have hperm : (g * w * g⁻¹) * w⁻¹ = 1 := by rw [hconj]; simp
  have hα : Induces ι (x * a * x⁻¹ * a⁻¹) 1 := by
    have h := ((hxg.mul haw).mul hxg.inv).mul haw.inv
    rw [hperm] at h
    exact h
  obtain ⟨α₀, hα₀⟩ := Induces.exists_eq_coordElt hC hα
  have hxa : x * a * x⁻¹ = coordElt ι α₀ * a := mul_inv_eq_iff_eq_mul.mp hα₀
  have hx3 : (x * a * x⁻¹) ^ 3 = 1 := by
    have h3 : (x * a * x⁻¹) ^ 3 = x * a ^ 3 * x⁻¹ := conj_pow
    rw [h3, ha3]; group
  have hcube : (coordElt ι α₀ * a) ^ 3 = 1 := by
    rw [← hxa]; exact hx3
  have hexp : (coordElt ι α₀ * a) ^ 3
      = coordElt ι (α₀ + w α₀ + w (w α₀)) := by
    have hstep : (coordElt ι α₀ * a) ^ 3
        = coordElt ι α₀ * (a * coordElt ι α₀ * a⁻¹)
            * (a * (a * coordElt ι α₀ * a⁻¹) * a⁻¹) * a ^ 3 := by
      rw [pow_three, pow_three]
      group
    rw [hstep, haw α₀, haw (w α₀), ha3, mul_one, ← coordElt_add, ← coordElt_add]
  have hce : coordElt ι (α₀ + w α₀ + w (w α₀)) = coordElt ι 0 := by
    rw [← hexp, hcube, coordElt_zero]
  have hsum : α₀ + w α₀ + w (w α₀) = 0 := coordElt_injective hι hce
  have hzero : w α₀ + α₀ + w (w α₀) = 0 := by
    rw [add_comm (w α₀) α₀]
    exact hsum
  have hvec : w α₀ + α₀ = w (w α₀) := eq_of_add_eq_zero_V6 hzero
  refine ⟨w α₀, ?_⟩
  calc coordElt ι (w α₀) * x * a
      = coordElt ι (w α₀) * (x * a * x⁻¹) * x := by group
    _ = coordElt ι (w α₀) * (coordElt ι α₀ * a) * x := by rw [hxa]
    _ = coordElt ι (w α₀) * coordElt ι α₀ * a * x := by group
    _ = coordElt ι (w α₀ + α₀) * a * x := by rw [← coordElt_add]
    _ = coordElt ι (w (w α₀)) * a * x := by rw [hvec]
    _ = a * coordElt ι (w α₀) * x := by rw [← haw (w α₀)]; group
    _ = a * (coordElt ι (w α₀) * x) := by group

theorem card_eq_mul_indGroup (hι : Function.Injective ι)
    (hC : centralizer (ι.range : Set G) ≤ ι.range) {K : Subgroup G} (hK : K ≤ indSub ι ⊤) :
    Nat.card K = Nat.card ↥(K ⊓ ι.range) * Nat.card (indGroup ι K) := by
  have hex : ∀ x : ↥K, ∃ g : Equiv.Perm V6, Induces ι x.1 g := by
    intro x
    obtain ⟨g, -, hg⟩ := mem_indSub.mp (hK x.2)
    exact ⟨g, hg⟩
  let f : ↥K → Equiv.Perm V6 := fun x => Classical.choose (hex x)
  have hf : ∀ x : ↥K, Induces ι x.1 (f x) := fun x => Classical.choose_spec (hex x)
  let φ : ↥K →* Equiv.Perm V6 :=
    { toFun := f
      map_one' := by
        apply Induces.unique hι (hf 1)
        exact induces_one
      map_mul' := fun x y => by
        exact Induces.unique hι (hf (x * y)) ((hf x).mul (hf y)) }
  have hrange : φ.range = indGroup ι K := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_indGroup.mpr ⟨x.1, x.2, hf x⟩
    · rintro hg
      obtain ⟨y, hy, hgy⟩ := mem_indGroup.mp hg
      exact ⟨⟨y, hy⟩, Induces.unique hι (hf ⟨y, hy⟩) hgy⟩
  have hker : φ.ker = (K ⊓ ι.range).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hind : Induces ι x.1 1 := by
        rw [← hx]
        exact hf x
      obtain ⟨v, hv⟩ := Induces.exists_eq_coordElt hC hind
      refine ⟨x.2, ?_⟩
      rw [hv]
      exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, rfl⟩
    · rintro ⟨-, hxr⟩
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxr
      apply Induces.unique hι (hf x)
      rw [← ha, show ι a = coordElt ι (Multiplicative.toAdd a) from by rw [coordElt, ofAdd_toAdd]]
      exact induces_coordElt _
  have hker_card : Nat.card ((K ⊓ ι.range).subgroupOf K) = Nat.card ↥(K ⊓ ι.range) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ ι.range ≤ K)).toEquiv
  have hiso := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, hker_card] at hiso
  exact hiso.symm

theorem card_eq_mul_of_lift {K : Subgroup G} {Hg : Subgroup (Equiv.Perm V6)}
    (hι : Function.Injective ι) (hC : centralizer (ι.range : Set G) ≤ ι.range)
    (hKle : K ≤ indSub ι Hg) (hlift : ∀ g ∈ Hg, ∃ x ∈ K, Induces ι x g) :
    Nat.card K = Nat.card ↥(K ⊓ ι.range) * Nat.card Hg := by
  have hmono : indSub ι Hg ≤ indSub ι ⊤ := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := mem_indSub.mp hx
    exact mem_indSub.mpr ⟨g, Subgroup.mem_top g, hgx⟩
  have hKtop : K ≤ indSub ι ⊤ := fun x hx => hmono (hKle hx)
  have hrange : indGroup ι K = Hg := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, hgx⟩ := mem_indGroup.mp hg
      exact Induces.mem_of_mem_indSub hι (hKle hx) hgx
    · intro hg
      obtain ⟨x, hx, hgx⟩ := hlift g hg
      exact mem_indGroup.mpr ⟨x, hx, hgx⟩
  rw [card_eq_mul_indGroup hι hC hKtop, hrange]

end CFSG.EvenSporadicStandard.HNRecog.Harada
