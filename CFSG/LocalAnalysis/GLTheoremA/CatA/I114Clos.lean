module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem closureIn_le_of_le {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) :
    closureIn K B ≤ X := by
  show (⨆ (a : G) (_ : a ∈ B), K.map (MulAut.conj a).toMonoidHom) ≤ X
  refine iSup₂_le fun a ha => ?_
  rintro _ ⟨k, hk, rfl⟩
  exact X.mul_mem (X.mul_mem (hBX ha) (hKX hk)) (X.inv_mem (hBX ha))

abbrev Sbar (p : ℕ) (X K B : Subgroup G) : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) :=
  ⨆ (b : ↥X ⧸ GLAPPrimeCore p ↥X) (_ : b ∈ barX p X B), cj b (barX p X K)

theorem mem_cj_conj_of_mem {Y : Type} [Group Y] {H : Subgroup Y} {g c : Y} (hc : c ∈ H) :
    g * c * g⁻¹ ∈ cj g H := by
  have e : g⁻¹ * (g * c * g⁻¹) * g = c := by group
  rw [mem_cj, e]
  exact hc

theorem mk_mem_Sbar_of_mem_closureIn {p : ℕ} {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X)
    {x : ↥X} (hx : x.1 ∈ closureIn K B) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) x : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ Sbar p X K B := by
  let Ssub : Subgroup G :=
    ((Sbar p X K B).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype
  have hle : closureIn K B ≤ Ssub := by
    show (⨆ (a : G) (_ : a ∈ B), K.map (MulAut.conj a).toMonoidHom) ≤ Ssub
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨k, hk, rfl⟩
    have hax : a ∈ X := hBX ha
    have hkx : k ∈ X := hKX hk
    refine Subgroup.mem_map.2 ⟨⟨a, hax⟩ * ⟨k, hkx⟩ * (⟨a, hax⟩ : ↥X)⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hc : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hkx⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
        barX p X K :=
      Subgroup.mem_map.2 ⟨⟨k, hkx⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    have hb : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, hax⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
        barX p X B :=
      Subgroup.mem_map.2 ⟨⟨a, hax⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    have hmem := mem_cj_conj_of_mem (g := (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, hax⟩ :
      ↥X ⧸ GLAPPrimeCore p ↥X)) hc
    exact (le_iSup₂ (f := fun (b : ↥X ⧸ GLAPPrimeCore p ↥X) (_ : b ∈ barX p X B) =>
      cj b (barX p X K)) _ hb) hmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hle hx)
  have hyeq : y = x := Subtype.ext hyx
  rw [hyeq] at hy
  exact Subgroup.mem_comap.1 hy

theorem map_subgroupOf_le_Sbar {p : ℕ} {X K B T : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X)
    (hT : T ≤ closureIn K B) :
    (T.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ≤ Sbar p X K B := by
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_Sbar_of_mem_closureIn hKX hBX (hT (Subgroup.mem_subgroupOf.1 hx))

theorem isPGroup_map_subgroupOf {p : ℕ} {X T : Subgroup G} (hTp : IsPGroup 2 T) :
    IsPGroup 2 ((T.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))) :=
  (hTp.comap_subtype (K := X)).map _

theorem mem_map_mk_iff {X : Type} [Group X] {N Tm : Subgroup X} [N.Normal] (z : X) :
    (QuotientGroup.mk' N z : X ⧸ N) ∈ Tm.map (QuotientGroup.mk' N) ↔ z ∈ Tm ⊔ N := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem mk_mem_normalizer_map {X : Type} [Group X] {N Tm : Subgroup X} [N.Normal] {x : X}
    (hx : x ∈ Subgroup.normalizer ((Tm ⊔ N : Subgroup X) : Set X)) :
    (QuotientGroup.mk' N x : X ⧸ N) ∈
      Subgroup.normalizer ((Tm.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N y
  have e : QuotientGroup.mk' N x * QuotientGroup.mk' N z * (QuotientGroup.mk' N x)⁻¹ =
      QuotientGroup.mk' N (x * z * x⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e, mem_map_mk_iff, mem_map_mk_iff]
  exact Subgroup.mem_normalizer_iff.1 hx z

theorem mem_normalizer_sup_of_mem {p : ℕ} {X T B : Subgroup G} (hBT : B ≤ Subgroup.normalizer (T : Set G))
    {x : ↥X} (hx : x.1 ∈ B) :
    x ∈ Subgroup.normalizer ((((T.subgroupOf X) ⊔ GLAPPrimeCore p ↥X : Subgroup ↥X)) : Set ↥X) := by
  rw [mem_normalizer_iff_cj]
  have hxT : x ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' : x.1 ∈ Subgroup.normalizer (T : Set G) := hBT hx
    rw [Subgroup.mem_normalizer_iff] at hx'
    have := hx' h.1
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hxN : x ∈ Subgroup.normalizer ((GLAPPrimeCore p ↥X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact Subgroup.mem_top x
  rw [cj_sup, mem_normalizer_iff_cj.1 hxT, mem_normalizer_iff_cj.1 hxN]

theorem barX_le_normalizer_map {p : ℕ} {X B T : Subgroup G} (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    barX p X B ≤ Subgroup.normalizer
      (((T.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :
        Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  exact mk_mem_normalizer_map (mem_normalizer_sup_of_mem hBT (Subgroup.mem_subgroupOf.1 hx))

theorem le_glaPPrimeCoreOf_closureIn {p : ℕ} (hp : p.Prime) {X K B T : Subgroup G}
    (hKX : K ≤ X) (hBX : B ≤ X) (hTcl : T ≤ closureIn K B)
    (h : (T.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥) :
    T ≤ GLAPPrimeCoreOf p (closureIn K B) := by
  have hTX : T ≤ X := le_trans hTcl (closureIn_le_of_le hKX hBX)
  have hO : T ≤ GLAPPrimeCoreOf p X := by
    intro t ht
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨t, hTX ht⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
        (T.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
    rw [h, Subgroup.mem_bot] at hmem
    have hn : (⟨t, hTX ht⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 hmem
    exact Subgroup.mem_map.2 ⟨⟨t, hTX ht⟩, hn, rfl⟩
  intro t ht
  exact CFSG.LocalAnalysis.GLTheoremB.inf_glaPPrimeCoreOf_le hp (closureIn_le_of_le hKX hBX)
    ⟨hTcl ht, hO ht⟩

end CFSG.LocalAnalysis.GLTheoremA.I114
