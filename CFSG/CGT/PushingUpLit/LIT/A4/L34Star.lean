module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34One

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

theorem klein_comm {U : Subgroup G} (hU : IsKleinFour ↥U) {u v : G} (hu : u ∈ U) (hv : v ∈ U) :
    u * v = v * u := by
  have := (IsKleinFour.isMulCommutative (G := ↥U)).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
  exact congrArg Subtype.val this

theorem Blk3.le_of_squares {X : Subgroup G} {a : G} (h : Blk3 X a) {N : Subgroup G}
    (hN : ∀ x ∈ X, x * x ∈ N) : X ≤ N := by
  have h3 : a * a * a = 1 := by
    have := h.cube
    simpa [pow_succ] using this
  have haN : a ∈ N := by
    have h2 : (a * a) * (a * a) ∈ N := hN _ (X.mul_mem h.mem h.mem)
    have e : (a * a) * (a * a) = a := by
      calc (a * a) * (a * a) = (a * a * a) * a := by group
        _ = a := by rw [h3, one_mul]
    rwa [e] at h2
  have hVN : ∀ v ∈ pCoreOf 2 X, v ∈ N := by
    intro v hv
    have hw : a * v * a⁻¹ ∈ pCoreOf 2 X := Blk3.conj_mem h hv
    have hwa : (a * v * a⁻¹) * a ∈ X := X.mul_mem ((pCoreOf_le_self X) hw) h.mem
    have h1 : ((a * v * a⁻¹) * a) * ((a * v * a⁻¹) * a) ∈ N := hN _ hwa
    have hn := Blk3.norm_eq_one h hv
    have hy₂ : a * (a * v * a⁻¹) * a⁻¹ ∈ pCoreOf 2 X := Blk3.conj_mem h hw
    have c1 : v * (a * v * a⁻¹) = (a * v * a⁻¹) * v := h.comm _ hv _ hw
    have e2 : (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) = v := by
      have h4 : (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) = v⁻¹ :=
        eq_inv_of_mul_eq_one_right (by simpa [mul_assoc] using hn)
      rw [h4]
      exact Blk3.inv_eq h hv
    have e1 : ((a * v * a⁻¹) * a) * ((a * v * a⁻¹) * a) =
        ((a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹)) * (a * a) := by group
    have haa : a * a ∈ N := N.mul_mem haN haN
    have : v = (((a * v * a⁻¹) * a) * ((a * v * a⁻¹) * a)) * (a * a)⁻¹ := by
      rw [e1, e2]
      group
    rw [this]
    exact N.mul_mem h1 (N.inv_mem haa)
  intro x hx
  obtain ⟨y, hy, j, rfl⟩ := h.dec x hx
  exact N.mul_mem (hVN y hy) (N.pow_mem haN j)

theorem lemma1c {X : Subgroup G} {a : G} (hb : Blk3 X a) {N : Subgroup G} {u v : G}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hCu : Subgroup.centralizer ({u} : Set G) ≤ N)
    (hCv : Subgroup.centralizer ({v} : Set G) ≤ N)
    (hCuv : Subgroup.centralizer ({u * v} : Set G) ≤ N)
    (hcom1 : ∀ x ∈ X, ∀ y ∈ conjSub u X, x * y = y * x)
    (hcom2 : ∀ x ∈ conjSub u X, ∀ y ∈ conjSub (u * v) X, x * y = y * x)
    (hcom3 : ∀ x ∈ X, ∀ y ∈ conjSub (u * v) X, x * y = y * x) : X ≤ N := by
  apply Blk3.le_of_squares hb
  intro x hx
  have hxu : u * x * u⁻¹ ∈ conjSub u X := conj_mem_conjSub hx
  have hxuv : (u * v) * x * (u * v)⁻¹ ∈ conjSub (u * v) X := conj_mem_conjSub hx
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu, hv, one_mul]
  have ha : x * (u * x * u⁻¹) ∈ N := hCu (mul_conj_mem_centralizer hu (hcom1 x hx _ hxu))
  have hc3 : x * ((u * v) * x * (u * v)⁻¹) = ((u * v) * x * (u * v)⁻¹) * x := hcom3 x hx _ hxuv
  have hc : ((u * v) * x * (u * v)⁻¹) * x ∈ N := by
    rw [← hc3]
    exact hCuv (mul_conj_mem_centralizer huv2 hc3)
  have hyu : (u * x * u⁻¹)⁻¹ ∈ conjSub u X := (conjSub u X).inv_mem hxu
  have hvy : v * (u * x * u⁻¹)⁻¹ * v⁻¹ ∈ conjSub (u * v) X := by
    have h1 : v * (u * x * u⁻¹)⁻¹ * v⁻¹ ∈ conjSub v (conjSub u X) := conj_mem_conjSub hyu
    rwa [conjSub_conjSub, show v * u = u * v from huv.symm] at h1
  have hb' : (u * x * u⁻¹)⁻¹ * (v * (u * x * u⁻¹)⁻¹ * v⁻¹) ∈ N :=
    hCv (mul_conj_mem_centralizer hv (hcom2 _ hyu _ hvy))
  have e : v * (u * x * u⁻¹)⁻¹ * v⁻¹ = ((u * v) * x * (u * v)⁻¹)⁻¹ := by
    rw [huv]
    group
  have key : (x * (u * x * u⁻¹)) * ((u * x * u⁻¹)⁻¹ * (v * (u * x * u⁻¹)⁻¹ * v⁻¹)) *
      (((u * v) * x * (u * v)⁻¹) * x) = x * x := by
    rw [e]
    group
  rw [← key]
  exact N.mul_mem (N.mul_mem ha hb') hc

theorem centralizer_conj_le {g z : G} {M : Subgroup G}
    (h : Subgroup.centralizer ({g⁻¹ * z * g} : Set G) ≤ M) :
    Subgroup.centralizer ({z} : Set G) ≤ conjSub g M := by
  intro c hc
  rw [mem_conjSub_iff]
  apply h
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  calc (g⁻¹ * c * g) * (g⁻¹ * z * g) = g⁻¹ * (c * z) * g := by group
    _ = g⁻¹ * (z * c) * g := by rw [hzc]
    _ = (g⁻¹ * z * g) * (g⁻¹ * c * g) := by group

section FamSection

structure Fam (M : Subgroup G) (𝒳 : Set (Subgroup G)) : Prop where
  blk : ∀ Y ∈ 𝒳, ∃ a, Blk3 Y a
  le : ∀ Y ∈ 𝒳, Y ≤ M
  comm : ∀ Y ∈ 𝒳, ∀ Y' ∈ 𝒳, Y ≠ Y' → ∀ x ∈ Y, ∀ y ∈ Y', x * y = y * x
  perm : ∀ k ∈ M, ∀ Y ∈ 𝒳, conjSub k Y ∈ 𝒳
  conj_le : ∀ Y ∈ 𝒳, ∀ g : G, conjSub g Y ≤ M → g ∈ M
  cent : ∀ z : G, z ≠ 1 → z * z = 1 → (∃ Y ∈ 𝒳, ∀ x ∈ Y, z * x = x * z) →
    Subgroup.centralizer ({z} : Set G) ≤ M
  two : ∃ Y ∈ 𝒳, ∃ Y' ∈ 𝒳, Y ≠ Y'

namespace Fam

variable {M : Subgroup G} {𝒳 : Set (Subgroup G)} (F : Fam M 𝒳)
include F

theorem conj (g : G) : Fam (conjSub g M) (conjSub g '' 𝒳) where
  blk := by
    rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨a, ha⟩ := F.blk Y hY
    exact ⟨g * a * g⁻¹, Blk3.conj ha g⟩
  le := by
    rintro _ ⟨Y, hY, rfl⟩
    exact conjSub_mono (F.le Y hY)
  comm := by
    rintro _ ⟨Y, hY, rfl⟩ _ ⟨Y', hY', rfl⟩ hne x hx y hy
    have hne' : Y ≠ Y' := fun e => hne (by rw [e])
    have hx' : g⁻¹ * x * g ∈ Y := mem_conjSub_iff.1 hx
    have hy' : g⁻¹ * y * g ∈ Y' := mem_conjSub_iff.1 hy
    have := F.comm Y hY Y' hY' hne' _ hx' _ hy'
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  perm := by
    rintro k hk _ ⟨Y, hY, rfl⟩
    have hk' : g⁻¹ * k * g ∈ M := mem_conjSub_iff.1 hk
    refine ⟨conjSub (g⁻¹ * k * g) Y, F.perm _ hk' Y hY, ?_⟩
    exact (Two.conjSub_conjSub_conj g k Y).symm
  conj_le := by
    rintro _ ⟨Y, hY, rfl⟩ k hk
    rw [Two.conjSub_conjSub_conj g k Y] at hk
    have h1 := conjSub_mono (g := g⁻¹) hk
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1
    exact mem_conjSub_iff.2 (F.conj_le Y hY _ h1)
  cent := by
    rintro z hz1 hz2 ⟨_, ⟨Y, hY, rfl⟩, hz⟩
    have hz1' : g⁻¹ * z * g ≠ 1 := fun e =>
      hz1 (conj_eq_one_iff.1 (show g⁻¹ * z * g⁻¹⁻¹ = 1 by simpa using e))
    have hz2' : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hz2]; group
    have hzc : ∀ x ∈ Y, (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g) := by
      intro x hx
      have hzx := hz _ (conj_mem_conjSub (g := g) hx)
      calc (g⁻¹ * z * g) * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [hzx]
        _ = x * (g⁻¹ * z * g) := by group
    exact centralizer_conj_le (F.cent _ hz1' hz2' ⟨Y, hY, hzc⟩)
  two := by
    obtain ⟨Y, hY, Y', hY', hne⟩ := F.two
    exact ⟨conjSub g Y, ⟨Y, hY, rfl⟩, conjSub g Y', ⟨Y', hY', rfl⟩,
      fun e => hne (conjSub_injective g e)⟩

end Fam

variable {M : Subgroup G} {𝒳 : Set (Subgroup G)}

theorem lemma1star [Finite G] (F : Fam M 𝒳) {N U : Subgroup G} (hUM : U ≤ M)
    (hU : IsKleinFour ↥U) (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ N)
    (hN : ∀ Y ∈ 𝒳, ¬ Y ≤ N) : ∀ Y ∈ 𝒳, pCoreOf 2 Y ≤ N := by
  intro Y hY
  obtain ⟨a, ha⟩ := F.blk Y hY
  have hsq : ∀ u ∈ U, u * u = 1 := fun u hu => klein_sq hU hu
  by_cases h1 : ∀ u ∈ U, conjSub u Y = Y
  · exact lemma1a ha hU h1 hC
  · push Not at h1
    obtain ⟨u, huU, hu⟩ := h1
    have hu1 : u ≠ 1 := fun e => hu (by rw [e, conjSub_one])
    have hY'𝒳 : conjSub u Y ∈ 𝒳 := F.perm u (hUM huU) Y hY
    have hu₂ : conjSub u Y = conjSub u Y ∧ conjSub u (conjSub u Y) = Y := by
      refine ⟨rfl, ?_⟩
      rw [conjSub_conjSub, hsq u huU, conjSub_one]
    by_cases h2 : ∀ x ∈ U, conjSub x Y = Y ∨ conjSub x Y = conjSub u Y
    · exact (lemma1b ha (F.comm Y hY _ hY'𝒳 hu.symm) hu hU huU hu₂ h2 hC).1
    · exfalso
      push Not at h2
      obtain ⟨v, hvU, hv1, hv2⟩ := h2
      have hv1' : v ≠ 1 := fun e => hv1 (by rw [e, conjSub_one])
      have huv : u * v = v * u := klein_comm hU huU hvU
      have huvU : u * v ∈ U := U.mul_mem huU hvU
      have huv1 : u * v ≠ 1 := by
        intro e
        apply hv2
        have h3 : v = u⁻¹ := eq_inv_of_mul_eq_one_right e
        rw [h3]
        have : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u huU)
        rw [this]
      have hXuv : conjSub (u * v) Y ∈ 𝒳 := F.perm _ (hUM huvU) Y hY
      have hd1 : Y ≠ conjSub (u * v) Y := by
        intro e
        apply hv2
        have h3 : conjSub v Y = conjSub u⁻¹ (conjSub (u * v) Y) := by
          rw [conjSub_conjSub]
          congr 1
          group
        rw [h3, ← e]
        have : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u huU)
        rw [this]
      have hd2 : conjSub u Y ≠ conjSub (u * v) Y := by
        intro e
        apply hv1
        have h3 : conjSub (u * v) Y = conjSub u (conjSub v Y) := (conjSub_conjSub u v Y).symm
        rw [h3] at e
        exact (conjSub_injective u e).symm
      have hYN := lemma1c ha (N := N) (hsq u huU) (hsq v hvU) huv
        (hC u huU hu1) (hC v hvU hv1') (hC (u * v) huvU huv1)
        (F.comm Y hY _ hY'𝒳 hu.symm) (F.comm _ hY'𝒳 _ hXuv hd2) (F.comm Y hY _ hXuv hd1)
      exact hN Y hY hYN

theorem cor1star [Finite G] (F : Fam M 𝒳) {g : G} (hg : g ∉ M) {U : Subgroup G} (hUM : U ≤ M)
    (hU : IsKleinFour ↥U)
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ conjSub g M) :
    (∀ Y ∈ 𝒳, pCoreOf 2 Y ≤ conjSub g M) ∧ (∀ Y ∈ 𝒳, pCoreOf 2 (conjSub g Y) ≤ M) := by
  have hN1 : ∀ Y ∈ 𝒳, ¬ Y ≤ conjSub g M := by
    intro Y hY hle
    apply hg
    have h1 := conjSub_mono (g := g⁻¹) hle
    rw [conjSub_inv_conjSub] at h1
    have := F.conj_le Y hY g⁻¹ h1
    simpa using M.inv_mem this
  have h1 := lemma1star F hUM hU hC hN1
  refine ⟨h1, ?_⟩
  obtain ⟨Y₀, hY₀, Y₁, hY₁, hne⟩ := F.two
  obtain ⟨a₀, ha₀⟩ := F.blk Y₀ hY₀
  have hVsq : ∀ x ∈ pCoreOf 2 Y₀, x * x = 1 := ha₀.sq
  have hKlein : IsKleinFour ↥(pCoreOf 2 Y₀) := isKleinFour_of_card_four ha₀.card hVsq
  have hN2 : ∀ Y ∈ conjSub g '' 𝒳, ¬ Y ≤ M := by
    rintro _ ⟨Y, hY, rfl⟩ hle
    exact hg (F.conj_le Y hY g hle)
  have key := lemma1star (F.conj g) (N := M) (U := pCoreOf 2 Y₀) (h1 Y₀ hY₀) hKlein
    (fun v hv hv1 => F.cent v hv1 (hVsq v hv)
      ⟨Y₁, hY₁, fun x hx => F.comm Y₀ hY₀ Y₁ hY₁ hne v ((pCoreOf_le_self Y₀) hv) x hx⟩) hN2
  exact fun Y hY => key _ ⟨Y, hY, rfl⟩

end FamSection

end CFSG.CGT.PushingUpLit.A4.L34
