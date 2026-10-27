module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Yam

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

variable {G : Type} [Group G] [Finite G]

private lemma relIndex_two_mul_mem {H K : Subgroup G} (hH : H ≤ K)
    (hidx : H.relIndex K = 2) {a b : G} (haK : a ∈ K) (hbK : b ∈ K) (haH : a ∉ H)
    (hbH : b ∉ H) : a * b ∈ H := by
  have h2 : (H.subgroupOf K).index = 2 := hidx
  have key := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) h2
    (a := ⟨a, haK⟩) (b := ⟨b, hbK⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  exact key.mpr ⟨fun h => absurd h haH, fun h => absurd h hbH⟩

private lemma conjSub_conjSub (a b : G) (Y : Subgroup G) :
    conjSub a (conjSub b Y) = conjSub (a * b) Y := by
  ext x
  constructor
  · intro hx
    rw [mem_conjSub] at hx
    obtain ⟨y, hy, hay⟩ := hx
    rw [mem_conjSub] at hy
    obtain ⟨z, hz, hbz⟩ := hy
    rw [mem_conjSub]
    exact ⟨z, hz, by rw [← hay, ← hbz]; group⟩
  · intro hx
    rw [mem_conjSub] at hx
    obtain ⟨z, hz, haz⟩ := hx
    rw [mem_conjSub]
    refine ⟨b * z * b⁻¹, ?_, by rw [← haz]; group⟩
    rw [mem_conjSub]
    exact ⟨z, hz, rfl⟩

private lemma conjSub_one (Y : Subgroup G) : conjSub 1 Y = Y := by
  ext x
  rw [mem_conjSub]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← h]
    simpa using hy
  · intro hx
    exact ⟨x, hx, by group⟩

private lemma conjSub_eq_self_of_maps {M : Subgroup G} {k : G}
    (hkM : ∀ x ∈ M, k * x * k⁻¹ ∈ M) : conjSub k M = M := by
  have hle : conjSub k M ≤ M := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub.mp hx
    exact hkM y hy
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcard : Nat.card (conjSub k M) = Nat.card M :=
    Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
  exact le_of_eq hcard.symm

private lemma conjSub_mem_maxElemAbelian {M Y : Subgroup G} {k : G} (hMk : conjSub k M = M)
    (hY : Y ∈ maxElemAbelian M) : conjSub k Y ∈ maxElemAbelian M := by
  obtain ⟨hYM, hYel, hYmax⟩ := hY
  have hMk' : conjSub k⁻¹ M = M := by
    have h := congrArg (conjSub k⁻¹) hMk
    rw [conjSub_inv_conjSub] at h
    exact h.symm
  refine ⟨?_, isElemAbelian_conjSub hYel k, ?_⟩
  · rw [← hMk]
    exact Subgroup.map_mono hYM
  · intro Y' hYY' hY'M hY'el
    have hle : Y ≤ conjSub k⁻¹ Y' := by
      have h2 : conjSub k⁻¹ (conjSub k Y) ≤ conjSub k⁻¹ Y' := Subgroup.map_mono hYY'
      rwa [conjSub_inv_conjSub] at h2
    have hY'M' : conjSub k⁻¹ Y' ≤ M := by
      have h2 : conjSub k⁻¹ Y' ≤ conjSub k⁻¹ M := Subgroup.map_mono hY'M
      rwa [hMk'] at h2
    have heq : conjSub k⁻¹ Y' = Y :=
      hYmax (conjSub k⁻¹ Y') hle hY'M' (isElemAbelian_conjSub hY'el k⁻¹)
    have hthis : conjSub k (conjSub k⁻¹ Y') = conjSub k Y := by rw [heq]
    rwa [conjSub_conjSub_inv] at hthis

theorem y7a_elemAbelian_of_k {M U : Subgroup G} {k : G} (hM : IsPGroup 2 M) (hUM : U ≤ M)
    (hU : IsElemAbelian 2 U) (hidx : U.relIndex M = 2) (hk3 : k ^ 3 = 1)
    (hkM : ∀ x ∈ M, k * x * k⁻¹ ∈ M) (hkU : ¬ ∀ x ∈ U, k * x * k⁻¹ ∈ U) :
    IsElemAbelian 2 M := by
  let W : Subgroup G := conjSub k U
  have hf : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  have hWM : W ≤ M := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub.mp hx
    exact hkM y (hUM hy)
  have hWel : IsElemAbelian 2 W := isElemAbelian_conjSub hU k
  have hMk : conjSub k M = M := conjSub_eq_self_of_maps hkM
  have hidxW : W.relIndex M = 2 := by
    have hmap : M.map (MulAut.conj k).toMonoidHom = M := hMk
    calc W.relIndex M = (U.map (MulAut.conj k).toMonoidHom).relIndex M := rfl
      _ = (U.map (MulAut.conj k).toMonoidHom).relIndex
            (M.map (MulAut.conj k).toMonoidHom) := by rw [hmap]
      _ = U.relIndex M := Subgroup.relIndex_map_map_of_injective U M hf
      _ = 2 := hidx
  have hWU : ¬ W ≤ U := by
    intro hle
    apply hkU
    intro x hx
    exact hle (mem_conjSub.mpr ⟨x, hx, rfl⟩)
  have hprod : ∀ s ∈ M, ∃ a ∈ U, ∃ b ∈ W, s = a * b := by
    intro s hsM
    by_cases hsU : s ∈ U
    · exact ⟨s, hsU, 1, W.one_mem, by rw [mul_one]⟩
    · obtain ⟨w, hwW, hwU⟩ : ∃ w ∈ W, w ∉ U := by
        by_contra h
        apply hWU
        intro x hxW
        by_contra hxU
        exact h ⟨x, hxW, hxU⟩
      have hsw : s * w⁻¹ ∈ U :=
        relIndex_two_mul_mem hUM hidx hsM (M.inv_mem (hWM hwW)) hsU
          (fun h => hwU (by simpa using U.inv_mem h))
      exact ⟨s * w⁻¹, hsw, w, hwW, by group⟩
  by_cases hMab : IsMulCommutative M
  · refine ⟨hMab, fun x hx => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have ha2 : a * a = 1 := by
      have := hU.2 a ha
      rwa [pow_two] at this
    have hb2 : b * b = 1 := by
      have := hWel.2 b hb
      rwa [pow_two] at this
    have hab : a * b = b * a := by
      haveI := hMab
      exact congrArg Subtype.val (mul_comm' (⟨a, hUM ha⟩ : M) ⟨b, hWM hb⟩)
    rw [pow_two]
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  · have hnab : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x := by
      by_contra h
      exact hMab (IsMulCommutative.of_comm fun x y => Subtype.ext (by
        by_contra hxy
        exact h ⟨x, x.2, y, y.2, hxy⟩))
    have hcent : ∀ a ∈ U, a ∉ W → ∀ s ∈ M, s * a = a * s ↔ s ∈ U := by
      intro a haU haW s hsM
      constructor
      · intro hsa
        by_contra hsU
        have haM : a ∈ M := hUM haU
        have ha2 : a * a = 1 := by
          have := hU.2 a haU
          rwa [pow_two] at this
        have hxdec : ∀ x ∈ M, x ∈ U ∨ ∃ u ∈ U, x = s * u := by
          intro x hxM
          by_cases hxU : x ∈ U
          · exact Or.inl hxU
          · refine Or.inr ⟨s⁻¹ * x, ?_, by group⟩
            exact relIndex_two_mul_mem hUM hidx (M.inv_mem hsM) hxM
              (fun h => hsU (by simpa using U.inv_mem h)) hxU
        have hacent : ∀ x ∈ M, a * x = x * a := by
          intro x hxM
          rcases hxdec x hxM with hxU | ⟨u, huU, rfl⟩
          · exact hU.comm haU hxU
          · calc a * (s * u) = (a * s) * u := by group
              _ = (s * a) * u := by rw [← hsa]
              _ = s * (a * u) := by group
              _ = s * (u * a) := by rw [← hU.comm huU haU]
              _ = (s * u) * a := by group
        have hxdecW : ∀ x ∈ M, x ∈ W ∨ ∃ w ∈ W, x = a * w := by
          intro x hxM
          by_cases hxW : x ∈ W
          · exact Or.inl hxW
          · refine Or.inr ⟨a⁻¹ * x, ?_, by group⟩
            exact relIndex_two_mul_mem hWM hidxW (M.inv_mem haM) hxM
              (fun h => haW (by simpa using W.inv_mem h)) hxW
        have hMcomm : IsMulCommutative M := by
          refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
          simp only [Subgroup.coe_mul]
          rcases hxdecW (x : G) x.2 with hxW | ⟨w, hwW, hxw⟩
          · rcases hxdecW (y : G) y.2 with hyW | ⟨v, hvW, hyv⟩
            · exact hWel.comm hxW hyW
            · rw [hyv]
              calc (x : G) * (a * v) = ((x : G) * a) * v := by group
                _ = (a * x) * v := by rw [← hacent x (hWM hxW)]
                _ = a * (x * v) := by group
                _ = a * (v * x) := by rw [← hWel.comm hxW hvW]
                _ = (a * v) * x := by group
          · rw [hxw]
            rcases hxdecW (y : G) y.2 with hyW | ⟨v, hvW, hyv⟩
            · have h1 : (a * w) * y = a * (w * y) := by group
              have h2 : y * (a * w) = a * (w * y) := by
                calc y * (a * w) = (y * a) * w := by group
                  _ = (a * y) * w := by rw [hacent y (hWM hyW)]
                  _ = a * (y * w) := by group
                  _ = a * (w * y) := by rw [hWel.comm hwW hyW]
              rw [h1, h2]
            · rw [hyv]
              have h1 : (a * w) * (a * v) = w * v := by
                calc (a * w) * (a * v) = (w * a) * (a * v) := by
                      rw [hacent w (hWM hwW)]
                  _ = w * (a * a) * v := by group
                  _ = w * v := by rw [ha2, mul_one]
              have h2 : (a * v) * (a * w) = w * v := by
                calc (a * v) * (a * w) = (v * a) * (a * w) := by
                      rw [hacent v (hWM hvW)]
                  _ = v * (a * a) * w := by group
                  _ = v * w := by rw [ha2, mul_one]
                  _ = w * v := hWel.comm hvW hwW
              rw [h1, h2]
        exact absurd hMcomm hMab
      · intro hsU
        exact hU.comm hsU haU
    obtain ⟨-, hmax, -, -⟩ := y7a_yam79_21 hM hUM hWM hprod hU hWel hnab hcent
    have hWmem : W ∈ maxElemAbelian M := by
      rw [hmax]
      exact Or.inr rfl
    have hkWmem : conjSub k W ∈ maxElemAbelian M := conjSub_mem_maxElemAbelian hMk hWmem
    rw [hmax] at hkWmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hkWmem
    have hkkk : (k * k) * k = 1 := by simpa [pow_three'] using hk3
    rcases hkWmem with hkW | hkW
    · have h1 : conjSub k W = conjSub (k * k) U := by
        rw [show W = conjSub k U from rfl, conjSub_conjSub]
      have h2 : U = conjSub (k * k) U := by rw [← h1, hkW]
      have h3 : conjSub k U = U := by
        calc conjSub k U = conjSub k (conjSub (k * k) U) := by rw [← h2]
          _ = conjSub (k * (k * k)) U := by rw [conjSub_conjSub]
          _ = conjSub ((k * k) * k) U := by rw [mul_assoc]
          _ = U := by rw [hkkk, conjSub_one]
      have hWUeq : W = U := h3
      exact absurd (le_of_eq hWUeq) hWU
    · have hUX : conjSub k U = conjSub k W := by rw [hkW]
      have hUW : U = W := by
        have h := congrArg (conjSub k⁻¹) hUX
        rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h
      exact absurd (le_of_eq hUW.symm) hWU

end CFSG.OddStandard.HigherRank.YamadaG23
