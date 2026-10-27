module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceTorusLift
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding.SPLMSide

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}

theorem exists_rElement_torusLift {T : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G))
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (hcore : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M) {c : D1CzQuot p z}
    (hc : c ∈ splXt0 p M z)
    (hcT : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
      c * t * c⁻¹ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    {r : ℕ} (hr : r.Prime) (hcr : c ^ r = 1) :
    ∃ (c₀ : G) (hc₀ : c₀ ∈ Subgroup.centralizer ({z} : Set G)), c₀ ∈ M ∧
      QuotientGroup.mk' (primeComplementCore p) ⟨c₀, hc₀⟩ = c ∧
      (∀ t ∈ T, c₀ * t * c₀⁻¹ ∈ T) ∧ ∃ k : ℕ, c₀ ^ r ^ k = 1 := by
  set C := Subgroup.centralizer ({z} : Set G)
  set O' := primeComplementCore (G := C) p
  set π := QuotientGroup.mk' O'
  obtain ⟨g, hg, rfl⟩ := hc
  have hTp' : IsPGroup p (T.subgroupOf C) := hTp.comap_subtype
  have hgN : π g ∈ Subgroup.normalizer
      (((T.subgroupOf C).map π : Subgroup (D1CzQuot p z)) : Set (D1CzQuot p z)) := by
    rw [hTmap]
    exact mem_normalizer_of_conj_into hcT
  have hgsup := comap_normalizer_map_le_sup hp O' (primeComplementCore_coprime p) hTp'
    (Subgroup.mem_comap.mpr hgN)
  obtain ⟨o, ho, n, hn, hon⟩ := Subgroup.mem_sup_of_normal_left.mp hgsup
  have ho1 : π o = 1 := MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk'])
  have hπn : π n = π g := by rw [← hon, map_mul, ho1, one_mul]
  have hnM : (n : G) ∈ M := by
    have hoM : (o : G) ∈ M := hcore ((mem_primeComplementCore_iff_mem_glbPrimeCore p o).mp ho)
    have hgM : (g : G) ∈ M := (Subgroup.mem_subgroupOf.mp hg).2
    have heq : (n : G) = (o : G)⁻¹ * (g : G) := by rw [← hon]; simp
    rw [heq]
    exact M.mul_mem (M.inv_mem hoM) hgM
  obtain ⟨m, k, hk, hm⟩ := exists_rPart_map_eq π n hr (by rw [hπn]; exact hcr)
  refine ⟨((n ^ m : C) : G), (n ^ m).2, ?_, ?_, ?_, k, ?_⟩
  · rw [Subgroup.coe_pow]
    exact M.pow_mem hnM m
  · rw [← hπn, ← hm]
  · intro t ht
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hn m) ⟨t, hTC ht⟩).mp
      (Subgroup.mem_subgroupOf.mpr ht)
    simpa using Subgroup.mem_subgroupOf.mp h
  · rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]

theorem commute_of_rElement {T X : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hXT : X ≤ T)
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC))
    {c₀ : G} (hc₀ : c₀ ∈ Subgroup.centralizer ({z} : Set G)) (hcT : ∀ t ∈ T, c₀ * t * c₀⁻¹ ∈ T)
    (hcZ : ∀ x ∈ centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC),
      QuotientGroup.mk' (primeComplementCore p) ⟨c₀, hc₀⟩ * x =
        x * QuotientGroup.mk' (primeComplementCore p) ⟨c₀, hc₀⟩) :
    ∀ x ∈ X, c₀ * x = x * c₀ := by
  intro x hx
  set C := Subgroup.centralizer ({z} : Set G)
  set π := QuotientGroup.mk' (primeComplementCore (G := C) p)
  have hxC := hTC (hXT hx)
  have hπx : π ⟨x, hxC⟩ ∈ centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) :=
    hpair ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hmemC : c₀ * x * c₀⁻¹ ∈ C :=
    C.mul_mem (C.mul_mem hc₀ hxC) (C.inv_mem hc₀)
  have h := eq_of_mk_eq_torusLift hp hTp (hcT x (hXT hx)) (hXT hx) hmemC hxC (by
    change π (⟨c₀, hc₀⟩ * ⟨x, hxC⟩ * ⟨c₀, hc₀⟩⁻¹) = π ⟨x, hxC⟩
    rw [map_mul, map_mul, map_inv, hcZ _ hπx, mul_inv_cancel_right])
  exact mul_inv_eq_iff_eq_mul.mp h

theorem eq_or_eq_of_rElement {T X : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hXT : X ≤ T)
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC))
    {c₀ : G} (hc₀ : c₀ ∈ Subgroup.centralizer ({z} : Set G))
    (hirr : ∀ V : Subgroup (D1CzQuot p z), centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ≤ V →
      V ≤ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC →
      (∀ v ∈ V, QuotientGroup.mk' (primeComplementCore p) ⟨c₀, hc₀⟩ * v *
        (QuotientGroup.mk' (primeComplementCore p) ⟨c₀, hc₀⟩)⁻¹ ∈ V) →
      V = centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ∨
        V = (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) :
    ∀ W : Subgroup G, X ≤ W → W ≤ T → (∀ w ∈ W, c₀ * w * c₀⁻¹ ∈ W) → W = X ∨ W = T := by
  intro W hXW hWT hcW
  set C := Subgroup.centralizer ({z} : Set G)
  set π := QuotientGroup.mk' (primeComplementCore (G := C) p)
  set V := (W.subgroupOf C).map π
  have hZV : centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ≤ V := by
    rw [← hpair]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hXW (Subgroup.mem_subgroupOf.mp hx))
  have hVT : V ≤ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC := by
    rw [← hTmap]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hWT (Subgroup.mem_subgroupOf.mp hx))
  have hcV : ∀ v ∈ V, π ⟨c₀, hc₀⟩ * v * (π ⟨c₀, hc₀⟩)⁻¹ ∈ V := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨c₀, hc₀⟩ * w * ⟨c₀, hc₀⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    simpa using hcW _ (Subgroup.mem_subgroupOf.mp hw)
  rcases hirr V hZV hVT hcV with hV | hV
  · refine Or.inl (le_antisymm (fun w hw => ?_) hXW)
    have hwC := hTC (hWT hw)
    have hπw : π ⟨w, hwC⟩ ∈ V := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
    rw [hV] at hπw
    exact mem_of_mk_mem_centerOf hp hTp hXT hpair (hWT hw) hwC hπw
  · refine Or.inr (le_antisymm hWT fun t ht => ?_)
    have hπt : π ⟨t, hTC ht⟩ ∈ V := by
      rw [hV, ← hTmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht)
    obtain ⟨w, hw, hwt⟩ := hπt
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
    rwa [← eq_of_mk_eq_torusLift hp hTp (hWT hwW) ht w.2 (hTC ht) hwt]

end CFSG.AGLEmbedding.SPLMSide
