module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9BLayer2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem gen49bl_mem_sylow_iff {Y : Type} [Group Y] {K Q : Subgroup Y} {P : Subgroup K}
    (hP : P.map K.subtype = Q ⊓ K) (k : K) : k ∈ P ↔ (k : Y) ∈ Q := by
  constructor
  · intro hk
    have : (k : Y) ∈ P.map K.subtype := mem_map_of_mem _ hk
    rw [hP] at this
    exact this.1
  · intro hk
    have : (k : Y) ∈ Q ⊓ K := ⟨hk, k.2⟩
    rw [← hP] at this
    obtain ⟨k', hk', hkk'⟩ := this
    rwa [← Subtype.ext hkk']

namespace Gen49BHyp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {S R Γ : Subgroup Y} {x : Y}

theorem gen49bl_exists_inner (h : Gen49BHyp p S R Γ x) (hInn : KFactInnerAction)
    (hR0 : CFSG.pCore p Y = ⊥) {K : Subgroup Y} (hK : IsComponentOf K ⊤) {s : Y} (hs : s ∈ S) :
    ∃ g ∈ S ⊓ K, ∀ k ∈ K, s * k * s⁻¹ = g * k * g⁻¹ := by
  have hZ := h.gen49bl_center_eq_bot hR0 hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hcat : IsCatalogGroup K := h.catalog.simple_subgroup K hsimple hnonab
  obtain ⟨Q, hQ⟩ := h.gen49bl_exists_sylow
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  rw [hQ] at hP
  have hmem := gen49bl_mem_sylow_iff hP
  have hsN : s ∈ normalizer (K : Set Y) := h.gen49bl_mem_normalizer hK hs
  set φ : MulAut K := K.normalizerMonoidHom ⟨s, hsN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : Y) = s * k * s⁻¹ := fun _ => rfl
  obtain ⟨n, hn⟩ := h.sylow.isPGroup ⟨s, hs⟩
  have hφp : φ ^ (p ^ n) = 1 := by
    have h1 : (⟨s, hsN⟩ : normalizer (K : Set Y)) ^ (p ^ n) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [hφdef, ← map_pow, h1, map_one]
  have hPne : (P : Subgroup K) ≠ ⊥ := by
    intro hbot
    obtain ⟨t, ⟨htS, htK⟩, hto, -⟩ :=
      exists_mem_sylow_inf_component Fact.out h.gen49bl_ne_two h.core_eq_bot Q hK
    rw [hQ] at htS
    have h1 : (⟨t, htK⟩ : K) ∈ (P : Subgroup K) := (hmem _).mpr htS
    rw [hbot, mem_bot] at h1
    have h2 : t = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hto
    exact (Fact.out : p.Prime).one_lt.ne hto
  obtain ⟨g, hgP, hg⟩ := hInn p Fact.out h.gen49bl_ne_two K hsimple hnonab hcat P hPne
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (h.gen49bl_commute ((hmem a).mp a.2) ((hmem b).mp b.2))))
    φ ⟨n, hφp⟩
    (fun g hg => by
      have hsg : s * (g : Y) = g * s := h.gen49bl_commute hs ((hmem g).mp hg)
      ext m
      change s * ((g : Y) * m * (g : Y)⁻¹) * s⁻¹ = (g : Y) * (s * m * s⁻¹) * (g : Y)⁻¹
      calc s * ((g : Y) * m * (g : Y)⁻¹) * s⁻¹ = (s * g) * m * (s * g)⁻¹ := by group
        _ = (g * s) * m * (g * s)⁻¹ := by rw [hsg]
        _ = (g : Y) * (s * m * s⁻¹) * (g : Y)⁻¹ := by group)
  refine ⟨(g : Y), ⟨(hmem g).mp hgP, g.2⟩, fun k hk => ?_⟩
  have h1 := congrArg (fun ψ : MulAut K => ((ψ ⟨k, hk⟩ : K) : Y)) hg
  simpa [hφ] using h1

theorem gen49bl_le_layer (h : Gen49BHyp p S R Γ x) (hInn : KFactInnerAction)
    (hR0 : CFSG.pCore p Y = ⊥) : S ≤ CFSG.layer Y := by
  intro s hs
  have hcomp : ∀ K : CFSG.LocalCores.ComponentIndex Y, ∃ g ∈ S ⊓ K.1,
      ∀ k ∈ K.1, s * k * s⁻¹ = g * k * g⁻¹ := fun K =>
    h.gen49bl_exists_inner hInn hR0 ((CFSG.isComponent_iff_open K.1).mp K.2) hs
  choose g hgmem hg using hcomp
  let xs : ∀ K : CFSG.LocalCores.ComponentIndex Y, K.1 := fun K => ⟨g K, (hgmem K).2⟩
  have heE : CFSG.LocalCores.layerMul Y xs ∈ CFSG.layer Y := by
    rw [← CFSG.LocalCores.layerMul_range]
    exact ⟨xs, rfl⟩
  have hz : ∀ K : CFSG.LocalCores.ComponentIndex Y, ∀ k ∈ K.1,
      (s * (CFSG.LocalCores.layerMul Y xs)⁻¹) * k * (s * (CFSG.LocalCores.layerMul Y xs)⁻¹)⁻¹ =
        k := by
    intro K k hk
    have hk' : (g K)⁻¹ * k * g K ∈ K.1 :=
      K.1.mul_mem (K.1.mul_mem (K.1.inv_mem (hgmem K).2) hk) (hgmem K).2
    have hu := CFSG.LocalCores.commute_layerMul_update xs K hk'
    have he : CFSG.LocalCores.layerMul Y xs =
        g K * CFSG.LocalCores.layerMul Y (Function.update xs K 1) :=
      CFSG.LocalCores.layerMul_eq_mul_update xs K
    set u := CFSG.LocalCores.layerMul Y (Function.update xs K 1) with hu_def
    have h1 : (g K * u)⁻¹ * k * (g K * u) = (g K)⁻¹ * k * g K := by
      calc (g K * u)⁻¹ * k * (g K * u) = u⁻¹ * ((g K)⁻¹ * k * g K) * u := by group
        _ = u⁻¹ * (u * ((g K)⁻¹ * k * g K)) := by rw [mul_assoc u⁻¹, ← hu.eq, ← mul_assoc]
        _ = (g K)⁻¹ * k * g K := by group
    rw [he]
    calc (s * (g K * u)⁻¹) * k * (s * (g K * u)⁻¹)⁻¹
        = s * ((g K * u)⁻¹ * k * (g K * u)) * s⁻¹ := by group
      _ = s * ((g K)⁻¹ * k * g K) * s⁻¹ := by rw [h1]
      _ = g K * ((g K)⁻¹ * k * g K) * (g K)⁻¹ := hg K _ hk'
      _ = k := by group
  have hzE : s * (CFSG.LocalCores.layerMul Y xs)⁻¹ ∈ centralizer (CFSG.layer Y : Set Y) := by
    rw [mem_centralizer_iff]
    intro e he
    have hle : CFSG.layer Y ≤ centralizer ({s * (CFSG.LocalCores.layerMul Y xs)⁻¹} : Set Y) := by
      refine sSup_le fun K hK => fun k hk => ?_
      rw [mem_centralizer_singleton_iff]
      have := hz ⟨K, hK⟩ k hk
      calc k * (s * (CFSG.LocalCores.layerMul Y xs)⁻¹)
          = (s * (CFSG.LocalCores.layerMul Y xs)⁻¹) * k *
              (s * (CFSG.LocalCores.layerMul Y xs)⁻¹)⁻¹ *
              (s * (CFSG.LocalCores.layerMul Y xs)⁻¹) := by rw [this]
        _ = (s * (CFSG.LocalCores.layerMul Y xs)⁻¹) * k := by group
    exact mem_centralizer_singleton_iff.mp (hle he)
  rw [centralizer_layer_eq_bot_of_pCore_eq_bot h.core_eq_bot hR0, mem_bot, mul_inv_eq_one] at hzE
  rw [hzE]
  exact heE

theorem gen49bl_layer_sup_normalizer (h : Gen49BHyp p S R Γ x) (hInn : KFactInnerAction)
    (hR0 : CFSG.pCore p Y = ⊥) : CFSG.layer Y ⊔ normalizer (S : Set Y) = ⊤ := by
  obtain ⟨Q, hQ⟩ := h.sylow.of_le (h.gen49bl_le_layer hInn hR0) le_top
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  rw [sup_comm, ← hQ]
  exact Sylow.normalizer_sup_eq_top Q

end Gen49BHyp

end CFSG.LocalAnalysis.RankThreeTheoremC
