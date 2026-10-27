module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section Nonab

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem not_commutative_of_mem_S (hc : centerOf L = ⊥) (hRlt : thompsonJ S < S) {a : G}
    (ha : a ∈ S) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) :
    ¬ ∀ i ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G),
      ∀ j ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G), i * j = j * i := by
  intro hcomm
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRU, hUV⟩ := E.RUU hcfg hx hxS
  obtain ⟨hUe, hVe, hmax⟩ := E.elemU hcfg hx hxS
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  have haU : a ∈ Subgroup.normalizer (blockU L : Set G) := E.S_le_normalizer_U hcfg ha
  have haV : a ∈ Subgroup.normalizer (conjR (blockU L) x : Set G) := by
    rw [conjR_normalizer, mem_conjR]
    apply E.S_le_normalizer_U hcfg
    exact (Subgroup.mem_normalizer_iff.1 (E.TnS hcfg hx) a).1 ha
  have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
    ((lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl).resolve_right fun h => h.1 hc).2
  have hZc := E.card_Z_inf_centralizer hcfg hRlt (Z := lin2Z L (thompsonJ S)) rfl ha haR ha2
  rw [hZR] at hZc
  have hUcard : Nat.card (blockU L) = 2 ^ (2 * n) := by
    rw [E.card_U' hcfg, hc]; simp
  have hVcard : Nat.card (conjR (blockU L) x) = 2 ^ (2 * n) := by
    rw [card_conjR, hUcard]
  have hsq : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  have hgU := card_le_sq_card_centralizer hUe
    (fun v hv => (Subgroup.mem_normalizer_iff.1 haU v).1 hv) ha2
  have hgV := card_le_sq_card_centralizer hVe
    (fun v hv => (Subgroup.mem_normalizer_iff.1 haV v).1 hv) ha2
  rw [hUcard, hsq] at hgU
  rw [hVcard, hsq] at hgV
  have hU2n : 2 ^ n ≤ Nat.card (blockU L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 hgU
  have hV2n : 2 ^ n ≤
      Nat.card (conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 hgV
  have hn : 1 < n := hcfg.one_lt
  have hlt : 2 ^ (n / 2) < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hAel : IsElemAbelian 2 ((blockU L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      (conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G))) :=
    isElemAbelian_sup_commute (IsElemAbelian.mono inf_le_left hUe)
      (IsElemAbelian.mono inf_le_left hVe)
      (fun a' ha' b' hb' => hcomm a' ⟨hUR ha'.1, ha'.2⟩ b' ⟨hVR hb'.1, hb'.2⟩)
  have hAR : (blockU L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      (conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G)) ≤ thompsonJ S :=
    sup_le (inf_le_left.trans hUR) (inf_le_left.trans hVR)
  rcases hmax _ hAR hAel with hAU | hAV
  · have hle : conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G) ≤
        centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := fun y hy =>
      ⟨by rw [← hUV]; exact ⟨hAU (Subgroup.mem_sup_right hy), hy.1⟩, hy.2⟩
    have := Subgroup.card_le_of_le hle
    omega
  · have hle : blockU L ⊓ Subgroup.centralizer ({a} : Set G) ≤
        centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := fun y hy =>
      ⟨by rw [← hUV]; exact ⟨hy.1, hAV (Subgroup.mem_sup_left hy)⟩, hy.2⟩
    have := Subgroup.card_le_of_le hle
    omega

end Nonab

section CY

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem commutator_centralizes_conjR_Z (hc : centerOf L = ⊥) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) {g a : G} (ha : a ∈ conjR Z g) (ha1 : a ≠ 1)
    {P : Subgroup G} (hP : P ≤ Subgroup.centralizer ({a} : Set G)) (hP2 : IsPGroup 2 P)
    {p q : G} (hp : p ∈ P) (hq : q ∈ P) {z : G} (hz : z ∈ conjR Z g) :
    ⁅p, q⁆ * z = z * ⁅p, q⁆ := by
  have hTI : fusionIsTI (conjR Z g) := fusionIsTI_conjR (E.ZTI hcfg hZ) g
  have hNP : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (conjR Z g : Set G) :=
    centralizer_le_normalizer_of_TI hTI ha ha1
  have hNZ : Subgroup.normalizer (Z : Set G) = M := E.N_Z_eq_M hcfg hZ hc
  have hPM : P ≤ conjR M g := by
    have h := hNP
    rw [conjR_normalizer, hNZ] at h
    exact hP.trans h
  have hP0 : conjR P g⁻¹ ≤ M := by
    rw [conjR_le_iff, inv_inv]; exact hPM
  have hP02 : IsPGroup 2 (conjR P g⁻¹) := (isPGroup_conjR_iff 2).2 hP2
  obtain ⟨m, hm, hmT⟩ := exists_le_conjR_of_isSylowTwoOf hcfg.cs.setting.isSylowTwoOf_M hP0 hP02
  obtain ⟨t, -, hTt⟩ := (E.h17 G T M H S L D n hcfg Z hZ).2 hc
  have hTM : T ≤ Subgroup.normalizer (Z : Set G) := hNZ ▸ hcfg.T_le_M
  have hTN : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem
    intro u hu y hy
    refine ⟨T.mul_mem (T.mul_mem hu hy.1) (T.inv_mem hu), ?_⟩
    show u * y * u⁻¹ ∈ Subgroup.centralizer (Z : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z' hz'
    have hu' : u⁻¹ * z' * u ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hTM hu)) z').1 hz'
      simpa using this
    have hc' := Subgroup.mem_centralizer_iff.1 hy.2 _ hu'
    calc z' * (u * y * u⁻¹) = u * ((u⁻¹ * z' * u) * y) * u⁻¹ := by group
      _ = u * (y * (u⁻¹ * z' * u)) * u⁻¹ := by rw [hc']
      _ = (u * y * u⁻¹) * z' := by group
  have hTT := commutator_le_of_sup_zpowers inf_le_left hTN hTt
  have hmem : ∀ y ∈ P, m * (g * y * g⁻¹) * m⁻¹ ∈ T := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ conjR P g⁻¹ := by
      rw [mem_conjR, show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group]; exact hy
    exact mem_conjR.1 (hmT h1)
  have hp' := hmem p hp
  have hq' := hmem q hq
  have hcomm : ⁅m * (g * p * g⁻¹) * m⁻¹, m * (g * q * g⁻¹) * m⁻¹⁆ ∈
      T ⊓ Subgroup.centralizer (Z : Set G) :=
    hTT (Subgroup.commutator_mem_commutator hp' hq')
  obtain ⟨z₀, hz₀, rfl⟩ := mem_conjR_iff'.1 hz
  have hz₁ : m * z₀ * m⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 (hNZ ▸ hm) z₀).1 hz₀
  have h := Subgroup.mem_centralizer_iff.1 hcomm.2 _ hz₁
  have e : ⁅m * (g * p * g⁻¹) * m⁻¹, m * (g * q * g⁻¹) * m⁻¹⁆ = m * (g * ⁅p, q⁆ * g⁻¹) * m⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e] at h
  have h2 : z₀ * (g * ⁅p, q⁆ * g⁻¹) = (g * ⁅p, q⁆ * g⁻¹) * z₀ := by
    calc z₀ * (g * ⁅p, q⁆ * g⁻¹)
        = m⁻¹ * ((m * z₀ * m⁻¹) * (m * (g * ⁅p, q⁆ * g⁻¹) * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * (g * ⁅p, q⁆ * g⁻¹) * m⁻¹) * (m * z₀ * m⁻¹)) * m := by rw [h]
      _ = (g * ⁅p, q⁆ * g⁻¹) * z₀ := by group
  calc ⁅p, q⁆ * (g⁻¹ * z₀ * g) = g⁻¹ * ((g * ⁅p, q⁆ * g⁻¹) * z₀) * g := by group
    _ = g⁻¹ * (z₀ * (g * ⁅p, q⁆ * g⁻¹)) * g := by rw [h2]
    _ = (g⁻¹ * z₀ * g) * ⁅p, q⁆ := by group

end CY

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
