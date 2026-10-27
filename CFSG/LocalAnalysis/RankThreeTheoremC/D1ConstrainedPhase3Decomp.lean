module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedLift3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1ConstrainedReducedData3.exists_decomposition {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {E C : Subgroup (ReducedCentralizer p z)} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hdata : D1ConstrainedReducedData3 p P M z Pbar zbar)
    (hstr : ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {F L : Subgroup G} (hFP : F ≤ (P : Subgroup G)) (hFcard : Nat.card F = p ^ 3)
    (hFexp : ∀ x ∈ F, x ^ p = 1) (hFZ : (Subgroup.center F).map F.subtype = Subgroup.zpowers z)
    (eF : F ⧸ Subgroup.center F ≃* Multiplicative (Fin 2 → ZMod p))
    (hFL : F ≤ L) (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (F : Set G))).map (centerQuotientAction F eF)) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      ∃ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G), ∃ x ∈ L,
        ∃ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), c = y * x * o := by
  have hp : p.Prime := Fact.out
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hFC : F ≤ Subgroup.centralizer ({z} : Set G) := hFP.trans hPC
  obtain ⟨φ, hφ⟩ := CFSG.AGLEmbedding.exists_mulEquiv_map_mk _ hp hO (P.isPGroup'.to_le hFP) hFC
  let zC : Subgroup.centralizer ({z} : Set G) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzbar := hdata.zbar_eq zC rfl
  have hFZbar := CFSG.AGLEmbedding.map_center_eq_zpowers_mk _ hFC φ hφ (zC := zC) hFZ
  have hSLC : StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (Subgroup.normalizer (F : Set G))).map (centerQuotientAction F eF) :=
    hSL.trans (Subgroup.map_mono (Subgroup.comap_mono hLC))
  have hFE := hdata.map_sl_eq hstr hPC hFP hFcard hFexp hFZ eF hSLC
  have hSLbar := CFSG.AGLEmbedding.statedSL_le_map_mk _ hFC hLC φ hφ eF hSL
  have hCmap := hdata.map_inf_centralizer_eq hstr hPC hFP hFE
  subst hFE
  obtain ⟨e'', hSLbar'⟩ : ∃ e'' : ((F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p))) ⧸ Subgroup.center
        ((F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore p))) ≃* Multiplicative (Fin 2 → ZMod p),
      StatedSL 2 (ZMod p) ≤ (((L.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore p))).subgroupOf (Subgroup.normalizer
          (((F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore p)) : Subgroup _) : Set _))).map
        (centerQuotientAction _ e'') := ⟨_, hSLbar⟩
  rw [hzbar] at hFZbar
  have hrange := range_centerQuotientActionNormal_eq_statedSL hFZbar hdata.zbar_order e'' hSLbar'
    hdata.zbar_mem_center
  intro c hc
  let c₀ : Subgroup.centralizer ({z} : Set G) := ⟨c, hc⟩
  have hmem : centerQuotientActionNormal _ e''
      (QuotientGroup.mk' (primeComplementCore p) c₀)⁻¹ ∈ StatedSL 2 (ZMod p) := by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  obtain ⟨g, hgL, hga⟩ := hSLbar' hmem
  have hρg := centerQuotientActionNormal_eq _ e'' g
  have hker : (g : ReducedCentralizer p z)⁻¹ * (QuotientGroup.mk' (primeComplementCore p) c₀)⁻¹ ∈
      (centerQuotientActionNormal _ e'').ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρg, hga, inv_mul_cancel]
  have hpc : (g : ReducedCentralizer p z)⁻¹ *
      (QuotientGroup.mk' (primeComplementCore p) c₀)⁻¹ ∈ CFSG.pCore p (ReducedCentralizer p z) := by
    have h1 := (mem_ker_centerQuotientActionNormal hFZbar e'').mp hker
    rw [← hstr.ker_eq, mem_ker_centerQuotientActionNormal hFZbar e]
    exact h1
  rw [← hstr.sup_eq] at hpc
  obtain ⟨ebar, hebar, cbar, hcbar, hmul⟩ := exists_mul_eq_of_mem_sup_normal hpc
  obtain ⟨f₀, hf₀, rfl⟩ := hebar
  rw [← hCmap] at hcbar
  obtain ⟨y₀, hy₀, rfl⟩ := hcbar
  obtain ⟨l₀, hl₀, hl₀g⟩ := hgL
  have hl₀g' : QuotientGroup.mk' (primeComplementCore p) l₀ = (g : ReducedCentralizer p z) :=
    hl₀g
  have h1 : (QuotientGroup.mk' (primeComplementCore p) c₀)⁻¹ =
      QuotientGroup.mk' (primeComplementCore p) l₀ *
        (QuotientGroup.mk' (primeComplementCore p) f₀ *
          QuotientGroup.mk' (primeComplementCore p) y₀) := by
    rw [hmul, hl₀g']
    group
  have key : QuotientGroup.mk' (primeComplementCore p) ((l₀ * (f₀ * y₀))⁻¹) =
      QuotientGroup.mk' (primeComplementCore p) c₀ := by
    rw [map_inv, map_mul, map_mul, ← h1, inv_inv]
  have hn : ((l₀ * (f₀ * y₀))⁻¹)⁻¹ * c₀ ∈ primeComplementCore (G := Subgroup.centralizer
      ({z} : Set G)) p := QuotientGroup.eq.mp key
  refine ⟨(y₀ : G)⁻¹, ?_, (f₀ : G)⁻¹ * (l₀ : G)⁻¹, ?_, ((((l₀ * (f₀ * y₀))⁻¹)⁻¹ * c₀ :
    Subgroup.centralizer ({z} : Set G)) : G), ?_, ?_⟩
  · exact ((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)).inv_mem hy₀
  · exact L.mul_mem (L.inv_mem (hFL hf₀)) (L.inv_mem hl₀)
  · have hn' : ((l₀ * (f₀ * y₀))⁻¹)⁻¹ * c₀ ∈ (GLBPrimeCore p (Subgroup.centralizer
        ({z} : Set G))).subgroupOf (Subgroup.centralizer ({z} : Set G)) := by
      rw [CFSG.AGLEmbedding.glbPrimeCore_subgroupOf]
      exact hn
    exact hn'
  · have : (c₀ : G) = (y₀ : G)⁻¹ * ((f₀ : G)⁻¹ * (l₀ : G)⁻¹) *
        ((((l₀ * (f₀ * y₀))⁻¹)⁻¹ * c₀ : Subgroup.centralizer ({z} : Set G)) : G) := by
      simp only [Subgroup.coe_mul, inv_inv]
      group
    exact this

end CFSG.LocalAnalysis.RankThreeTheoremC
