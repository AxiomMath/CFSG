module

public import Mathlib.GroupTheory.Sylow

public section

open Subgroup
open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoCo1

variable {G : Type*} [Group G]

@[expose] noncomputable def sqCount (S : Subgroup G) (y : G) : ℕ :=
  Nat.card {s : S // (s : G) * s = y}

theorem sqCount_map {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    (S : Subgroup G) (y : G) : sqCount (S.map f) (f y) = sqCount S y := by
  symm
  refine Nat.card_congr ((S.equivMapOfInjective f hf).toEquiv.subtypeEquiv fun s => ?_)
  show (s : G) * s = y ↔ f s * f s = f y
  rw [← map_mul, hf.eq_iff]

theorem sqCount_conj (S : Subgroup G) {m : G} (hm : S.map (MulAut.conj m).toMonoidHom = S)
    (y : G) : sqCount S (m * y * m⁻¹) = sqCount S y := by
  have h := sqCount_map (MulAut.conj m).toMonoidHom (MulAut.conj m).injective S y
  rw [hm] at h
  exact h

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_eq_of_card {L S T : Subgroup G} (hSL : S ≤ L) (hTL : T ≤ L)
    (hS : Nat.card S = p ^ (Nat.card L).factorization p)
    (hT : Nat.card T = p ^ (Nat.card L).factorization p) :
    ∃ c ∈ L, S.map (MulAut.conj c).toMonoidHom = T := by
  have hS' : Nat.card (S.subgroupOf L) = p ^ (Nat.card L).factorization p := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hT' : Nat.card (T.subgroupOf L) = p ^ (Nat.card L).factorization p := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq L (Sylow.ofCard (S.subgroupOf L) hS')
    (Sylow.ofCard (T.subgroupOf L) hT')
  have hc' : MulAut.conj c • S.subgroupOf L = T.subgroupOf L := by
    have := congrArg (fun P : Sylow p L => (P : Subgroup L)) hc
    simpa [Sylow.coe_subgroup_smul] using this
  have hle : S.map (MulAut.conj (c : G)).toMonoidHom ≤ T := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (⟨s, hSL hs⟩ : L) ∈ S.subgroupOf L := hs
    have := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hs'
    rw [hc'] at this
    exact this
  refine ⟨c, c.2, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj (c : G)).injective]
  exact hT.trans hS.symm |>.le


theorem exists_sylow_centralizer {L : Subgroup G} {x : G} (hxL : x ∈ L) (hx : orderOf x = p)
    (hdvd : p ^ (Nat.card L).factorization p ∣
      Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G)) :
    ∃ S₀ : Subgroup G, S₀ ≤ L ∧ S₀ ≤ centralizer ({x} : Set G) ∧ x ∈ S₀ ∧
      Nat.card S₀ = p ^ (Nat.card L).factorization p := by
  set R : Subgroup G := L ⊓ centralizer ({x} : Set G) with hR
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p R))
  have hRL : Nat.card R ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_left
  have hfac : (Nat.card R).factorization p = (Nat.card L).factorization p := by
    refine le_antisymm
      ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hRL p) ?_
    exact ((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have hP₀ : Nat.card P₀ = p ^ (Nat.card L).factorization p := by
    rw [P₀.card_eq_multiplicity, hfac]
  have hxR : x ∈ R := ⟨hxL, mem_centralizer_singleton_iff.2 rfl⟩
  have hcomm : ∀ g : R, g * (⟨x, hxR⟩ : R) = ⟨x, hxR⟩ * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2.2)
  have hN : Subgroup.zpowers (⟨x, hxR⟩ : R) ≤ P₀ := by
    have : (Subgroup.zpowers (⟨x, hxR⟩ : R)).Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := hn
      refine ⟨k, ?_⟩
      show (⟨x, hxR⟩ : R) ^ k = g * (⟨x, hxR⟩ : R) ^ k * g⁻¹
      rw [(Commute.zpow_right (show Commute g ⟨x, hxR⟩ from hcomm g) k).eq, mul_inv_cancel_right]⟩
    refine IsPGroup.le_sylow_of_normal (IsPGroup.of_card (n := 1) ?_) P₀
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hx
  refine ⟨(P₀ : Subgroup R).map R.subtype, (Subgroup.map_subtype_le _).trans inf_le_left,
    (Subgroup.map_subtype_le _).trans inf_le_right, ⟨⟨x, hxR⟩, hN (Subgroup.mem_zpowers _), rfl⟩,
    ?_⟩
  rw [Subgroup.card_map_of_injective R.subtype_injective]
  exact hP₀

theorem exists_normalizer_fusion {L S : Subgroup G} {z h : G}
    (hCz : centralizer ({z} : Set G) = L) (hSL : S ≤ L)
    (hS : Nat.card S = p ^ (Nat.card L).factorization p)
    (hSc : S ≤ centralizer ({h * z * h⁻¹} : Set G)) :
    ∃ m : G, S.map (MulAut.conj m).toMonoidHom = S ∧ m * (h * z * h⁻¹) * m⁻¹ = z := by
  set S' : Subgroup G := S.map (MulAut.conj h⁻¹).toMonoidHom with hS'
  have hS'L : S' ≤ L := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hCz, mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hSc hs)
    have h2 := congrArg (fun t => h⁻¹ * t * h) h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc h⁻¹ * s * h * z = h⁻¹ * (s * (h * z * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * z * h⁻¹ * s) * h := h2
      _ = z * (h⁻¹ * s * h) := by group
  have hS'card : Nat.card S' = p ^ (Nat.card L).factorization p := by
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact hS
  obtain ⟨c, hcL, hc⟩ := exists_conj_eq_of_card hS'L hSL hS'card hS
  refine ⟨c * h⁻¹, ?_, ?_⟩
  · have : S.map (MulAut.conj (c * h⁻¹)).toMonoidHom = S'.map (MulAut.conj c).toMonoidHom := by
      rw [hS', Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this, hc]
  · have hcz : c * z = z * c :=
      mem_centralizer_singleton_iff.1 (by rw [hCz]; exact hcL)
    calc c * h⁻¹ * (h * z * h⁻¹) * (c * h⁻¹)⁻¹ = c * z * c⁻¹ := by group
      _ = z := by rw [hcz]; group

theorem exists_fusion_in_sylow {L S : Subgroup G} {z g : G} (hz : orderOf z = p)
    (hCz : centralizer ({z} : Set G) = L) (hSL : S ≤ L)
    (hS : Nat.card S = p ^ (Nat.card L).factorization p) (hxL : g * z * g⁻¹ ∈ L)
    (hdvd : p ^ (Nat.card L).factorization p ∣
      Nat.card (L ⊓ centralizer ({g * z * g⁻¹} : Set G) : Subgroup G)) :
    ∃ c ∈ L, c * (g * z * g⁻¹) * c⁻¹ ∈ S ∧
      S ≤ centralizer ({c * (g * z * g⁻¹) * c⁻¹} : Set G) ∧
      sqCount S (c * (g * z * g⁻¹) * c⁻¹) = sqCount S z := by
  have hx : orderOf (g * z * g⁻¹) = p := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    rw [hz] at this
    simpa [MulAut.conj_apply] using this
  obtain ⟨S₀, hS₀L, hS₀c, hxS₀, hS₀⟩ := exists_sylow_centralizer hxL hx hdvd
  obtain ⟨c, hcL, hc⟩ := exists_conj_eq_of_card hS₀L hSL hS₀ hS
  have hyS : c * (g * z * g⁻¹) * c⁻¹ ∈ S := by
    rw [← hc]
    exact ⟨_, hxS₀, rfl⟩
  have hSy : S ≤ centralizer ({c * (g * z * g⁻¹) * c⁻¹} : Set G) := by
    rw [← hc]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hS₀c hs)
    have h2 := congrArg (fun t => c * t * c⁻¹) h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * s * c⁻¹ * (c * (g * z * g⁻¹) * c⁻¹) = c * (s * (g * z * g⁻¹)) * c⁻¹ := by group
      _ = c * ((g * z * g⁻¹) * s) * c⁻¹ := h2
      _ = c * (g * z * g⁻¹) * c⁻¹ * (c * s * c⁻¹) := by group
  have hy : c * (g * z * g⁻¹) * c⁻¹ = c * g * z * (c * g)⁻¹ := by group
  obtain ⟨m, hm, hmz⟩ := exists_normalizer_fusion (h := c * g) hCz hSL hS (by rwa [← hy])
  refine ⟨c, hcL, hyS, hSy, ?_⟩
  rw [← sqCount_conj S hm, hy, hmz]

end CFSG.EvenSporadicStandard.TwoCo1
