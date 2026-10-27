module

public import CFSG.GH74.Generic.S3.NoOutZ
public import CFSG.GH74.Generic.S45.PumpC1
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup
open scoped commutatorElement

section Oc

variable {G : Type} [Group G]

@[expose] noncomputable def oc (u : G) : Subgroup G :=
  (pPrimeCore 2 ↥(centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype

theorem oc_conj (u : G) {c : G} (hc : c ∈ centralizer ({u} : Set G)) {o : G} (ho : o ∈ oc u) :
    c * o * c⁻¹ ∈ oc u := by
  obtain ⟨n, hn, rfl⟩ := ho
  exact ⟨⟨c, hc⟩ * n * ⟨c, hc⟩⁻¹, (inferInstance : (pPrimeCore 2 ↥(centralizer ({u} : Set G))).Normal).conj_mem n hn ⟨c, hc⟩, rfl⟩

theorem mem_oc_iff (u : G) {g : G} (hg : g ∈ centralizer ({u} : Set G)) :
    g ∈ oc u ↔ proj u ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨n, hn, hng⟩
    have : n = ⟨g, hg⟩ := Subtype.ext hng
    subst this
    exact (QuotientGroup.eq_one_iff _).2 hn
  · intro h
    exact ⟨⟨g, hg⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩

theorem oc_odd [Finite G] (u : G) : Odd (Nat.card (oc u)) := by
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) := pPrimeCore_coprime_card
  rw [oc, Subgroup.card_map_of_injective (centralizer ({u} : Set G)).subtype_injective]
  exact Nat.coprime_two_left.1 hcop

end Oc

section S4

variable {G : Type} [Group G] [Finite G]

theorem zStar_of_component {u x : G} (hxu : x * u = u * x) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    {Iv : Subgroup G} (hIv : Iv ≤ centralizer ({u} : Set G)) (hcomp : IsComponent (S45.barSub u Iv))
    (hxIv : ∀ i ∈ Iv, x * i = i * x)
    (hno : ∀ z : G, z * z = 1 → z * x = x * z → z * u = u * z → z ≠ x → IsConj x z →
        (∀ i ∈ Iv, z * i * z⁻¹ * i⁻¹ ∈ oc u) → False) :
    ∃ O : Subgroup G, O ≤ centralizer ({u} : Set G) ∧
      (∀ c ∈ centralizer ({u} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O) ∧ Odd (Nat.card O) ∧
      ∀ h ∈ centralizer ({u} : Set G), h * x * h⁻¹ * x⁻¹ ∈ O := by
  classical
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.2 hxu
  let xX : ↥C := ⟨x, hxC⟩
  have hxX2 : xX * xX = 1 := Subtype.ext hx2
  have hxX1 : xX ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  set Lb := S45.barSub u Iv with hLb
  set π := proj u with hπ
  have hxLb : ∀ l ∈ Lb, π xX * l = l * π xX := by
    intro l hl
    obtain ⟨g, hg, hgI, rfl⟩ := S45.mem_barSub.1 hl
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxIv g hgI)
  have hbad : ∀ n : ↥C, (∀ l ∈ Lb, π (n * xX * n⁻¹) * l = l * π (n * xX * n⁻¹)) →
      (n * xX * n⁻¹) * xX = xX * (n * xX * n⁻¹) → n * xX * n⁻¹ = xX := by
    intro n hcent hcomm
    by_contra hne
    set zX : ↥C := n * xX * n⁻¹ with hzX
    have hzz : zX * zX = 1 := by
      calc zX * zX = n * (xX * xX) * n⁻¹ := by rw [hzX]; group
        _ = 1 := by rw [hxX2]; group
    refine hno (zX : G) (congrArg Subtype.val hzz) (congrArg Subtype.val hcomm)
      (mem_centralizer_singleton_iff.1 zX.2) (fun h => hne (Subtype.ext h)) (isConj_iff.2 ⟨n, rfl⟩) ?_
    intro i hi
    have hiC : i ∈ C := hIv hi
    set iX : ↥C := ⟨i, hiC⟩ with hiX
    have h1 := hcent (π iX) (S45.proj_mem_barSub hiC hi)
    have h2 : π (zX * iX * zX⁻¹ * iX⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact (mem_oc_iff u (zX * iX * zX⁻¹ * iX⁻¹).2).2 h2
  set Nn : Subgroup ↥C := (normalizer (Lb : Set (CentralizerBar u))).comap π with hNn
  have hxNn : xX ∈ Nn := by
    show π xX ∈ normalizer (Lb : Set (CentralizerBar u))
    exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun l hl => (hxLb l hl).symm)
  have hconjLb : ∀ n : ↥C, n ∈ Nn → ∀ l ∈ Lb, ∃ l' ∈ Lb, l = π n * l' * (π n)⁻¹ := by
    intro n hn l hl
    refine ⟨(π n)⁻¹ * l * π n, ?_, by group⟩
    have h1 : π n ∈ normalizer (Lb : Set (CentralizerBar u)) := hn
    have h2 := ((Subgroup.mem_normalizer_iff.1 (inv_mem h1)) l).1 hl
    simpa using h2
  have hcentLb : ∀ n : ↥C, n ∈ Nn → ∀ l ∈ Lb, π (n * xX * n⁻¹) * l = l * π (n * xX * n⁻¹) := by
    intro n hn l hl
    obtain ⟨l', hl', rfl⟩ := hconjLb n hn l hl
    have := hxLb l' hl'
    calc π (n * xX * n⁻¹) * (π n * l' * (π n)⁻¹) = π n * (π xX * l') * (π n)⁻¹ := by
          rw [map_mul, map_mul, map_inv]; group
      _ = π n * (l' * π xX) * (π n)⁻¹ := by rw [this]
      _ = (π n * l' * (π n)⁻¹) * π (n * xX * n⁻¹) := by rw [map_mul, map_mul, map_inv]; group
  have hiso1 : ∀ n ∈ Nn, (n * xX * n⁻¹) * xX = xX * (n * xX * n⁻¹) → n * xX * n⁻¹ = xX :=
    fun n hn hcomm => hbad n (hcentLb n hn) hcomm
  obtain ⟨N, hNle, hNnorm, hNodd, hN⟩ := exists_odd_normal_of_isolated (G := ↥C) (Y := Nn) hxNn hxX2 hxX1 hiso1
  have hY : pPrimeCore 2 (CentralizerBar u) = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_two
  have hπsurj : Function.Surjective π := QuotientGroup.mk_surjective
  set O' : Subgroup (CentralizerBar u) := N.map π with hO'
  have hO'odd : Odd (Nat.card O') := Odd.of_dvd_nat hNodd (Subgroup.card_map_dvd _ _)
  have hO'norm : ∀ n ∈ normalizer (Lb : Set (CentralizerBar u)), ∀ o ∈ O', n * o * n⁻¹ ∈ O' := by
    intro nb hnb ob hob
    obtain ⟨n, rfl⟩ := hπsurj nb
    obtain ⟨o, ho, rfl⟩ := hob
    exact ⟨n * o * n⁻¹, hNnorm n hnb o ho, by rw [map_mul, map_mul, map_inv]⟩
  have hZ : ∀ n ∈ normalizer (Lb : Set (CentralizerBar u)), π xX * n * (π xX)⁻¹ * n⁻¹ ∈ O' := by
    intro nb hnb
    obtain ⟨n, rfl⟩ := hπsurj nb
    have h1 := hN n hnb
    refine ⟨xX * n * xX⁻¹ * n⁻¹, ?_, by rw [map_mul, map_mul, map_mul, map_inv, map_inv]⟩
    have h2 := inv_mem h1
    have e : (n * xX * n⁻¹ * xX⁻¹)⁻¹ = xX * n * xX⁻¹ * n⁻¹ := by group
    rwa [e] at h2
  have hconj := conj_centralizes_layer hY hcomp hO'odd hO'norm hZ
  have hiso2 : ∀ h ∈ (⊤ : Subgroup ↥C), (h * xX * h⁻¹) * xX = xX * (h * xX * h⁻¹) → h * xX * h⁻¹ = xX := by
    intro h _ hcomm
    refine hbad h (fun l hl => ?_) hcomm
    have := hconj (π h) l hl
    simpa [map_mul, map_inv] using this
  obtain ⟨N₂, -, hN₂norm, hN₂odd, hN₂⟩ := exists_odd_normal_of_isolated (G := ↥C) (Y := ⊤) (Subgroup.mem_top xX) hxX2 hxX1 hiso2
  refine ⟨N₂.map C.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, -, rfl⟩
    exact n.2
  · rintro c hc _ ⟨n, hn, rfl⟩
    exact ⟨⟨c, hc⟩ * n * ⟨c, hc⟩⁻¹, hN₂norm ⟨c, hc⟩ (Subgroup.mem_top _) n hn, rfl⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hN₂odd
  · intro h hh
    exact ⟨⟨h, hh⟩ * xX * ⟨h, hh⟩⁻¹ * xX⁻¹, hN₂ ⟨h, hh⟩ (Subgroup.mem_top _), rfl⟩

end S4

end CFSG.GH74.Generic.S3
