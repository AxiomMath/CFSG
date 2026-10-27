module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NW1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F : Subgroup G}

private lemma inv_mul_inv_comm {a b : G} (h : a * b = b * a) : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_inv_rev, ← mul_inv_rev, h]

private lemma mul_inv_comm {a b : G} (h : a * b = b * a) : b * a⁻¹ = a⁻¹ * b := by
  have hinv : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := inv_mul_inv_comm h
  calc b * a⁻¹ = (a⁻¹ * (a * b)) * a⁻¹ := by group
    _ = (a⁻¹ * (b * a)) * a⁻¹ := by rw [h]
    _ = a⁻¹ * b := by group

private lemma conj_conjSub_eq {t g v : G} (htg : t * g = g * t) :
    g * (t * v * t⁻¹) * g⁻¹ = t * (g * v * g⁻¹) * t⁻¹ := by
  calc g * (t * v * t⁻¹) * g⁻¹ = (g * t) * v * (t⁻¹ * g⁻¹) := by group
    _ = (t * g) * v * (t⁻¹ * g⁻¹) := by rw [← htg]
    _ = (t * g) * v * (g⁻¹ * t⁻¹) := by rw [inv_mul_inv_comm htg]
    _ = t * (g * v * g⁻¹) * t⁻¹ := by group

private lemma conj_comm_zpowers {t g v : G} (htg : t * g = g * t) (hgv : g * v = v * g) :
    g * (t * v * t⁻¹) = (t * v * t⁻¹) * g := by
  have hgtinv : g * t⁻¹ = t⁻¹ * g := mul_inv_comm htg
  calc g * (t * v * t⁻¹) = (g * t) * v * t⁻¹ := by group
    _ = (t * g) * v * t⁻¹ := by rw [← htg]
    _ = t * (g * v) * t⁻¹ := by group
    _ = t * (v * g) * t⁻¹ := by rw [hgv]
    _ = t * v * (g * t⁻¹) := by group
    _ = t * v * (t⁻¹ * g) := by rw [hgtinv]
    _ = (t * v * t⁻¹) * g := by group

private lemma Wr7.conj_mem_of_normalizes (h : Wr7 t P U) {g : G} (htg : t * g = g * t)
    (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U) {x : G} (hx : x ∈ P) : g * x * g⁻¹ ∈ P := by
  obtain ⟨u, hu, v', hv', hxuv⟩ := h.decomp hx
  obtain ⟨v, hv, hv'eq⟩ := (mem_conjSub_iff' t U v').mp hv'
  have hEq : g * (u * (t * v * t⁻¹)) * g⁻¹ =
      (g * u * g⁻¹) * (t * (g * v * g⁻¹) * t⁻¹) := by
    calc g * (u * (t * v * t⁻¹)) * g⁻¹
        = (g * u * g⁻¹) * (g * (t * v * t⁻¹) * g⁻¹) := by group
      _ = (g * u * g⁻¹) * (t * (g * v * g⁻¹) * t⁻¹) := by rw [conj_conjSub_eq htg]
  rw [hxuv, hv'eq, hEq]
  exact h.mul_mem' (hgU u hu)
    ((mem_conjSub_iff' t U _).mpr ⟨g * v * g⁻¹, hgU v hv, rfl⟩)

theorem y7n_coset_cover (h : Wr7 t P U) (hS : centEl P t = S) (hF : SgFacts S F g)
    (htg : t * g = g * t) (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    ∀ p ∈ P, (p * g) ^ 2 = 1 →
      ∃ E : Subgroup G, E ≤ P ⊔ zpowers g ∧ IsElemAbelian 2 E ∧ 64 ≤ Nat.card E ∧
        p * g ∈ E := by
  intro p hp hp2
  obtain ⟨FU, hFU_le, hFU_el, hFU_card, hFU_cent, hFU_inv⟩ := y7n_FU h hS hF htg hgU
  obtain ⟨u, hu, v', hv', hpuv⟩ := h.decomp hp
  obtain ⟨v, hv, hv'eq⟩ := (mem_conjSub_iff' t U v').mp hv'
  have hgv' : g * v' * g⁻¹ ∈ conjSub t U :=
    (mem_conjSub_iff' t U _).mpr ⟨g * v * g⁻¹, hgU v hv, by
      rw [hv'eq]; exact conj_conjSub_eq htg⟩
  have hgg : g * g = 1 := by simpa [pow_two] using hF.g_sq
  have hii : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hgg, inv_one]
  have hp1 : p * (g * p * g⁻¹) = 1 := by
    have h1 : (p * g) * (p * g) = 1 := by simpa [pow_two] using hp2
    calc p * (g * p * g⁻¹) = (p * g) * (p * g) * (g⁻¹ * g⁻¹) := by group
      _ = 1 := by rw [h1, hii, mul_one]
  have hconj : g * p * g⁻¹ = p⁻¹ := (inv_eq_of_mul_eq_one_right hp1).symm
  have hcomm_inv : v'⁻¹ * u⁻¹ = u⁻¹ * v'⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h.direct.2.2 u hu v' hv']
  have hconj' : (g * u * g⁻¹) * (g * v' * g⁻¹) = u⁻¹ * v'⁻¹ := by
    calc (g * u * g⁻¹) * (g * v' * g⁻¹) = g * (u * v') * g⁻¹ := by group
      _ = g * p * g⁻¹ := by rw [hpuv]
      _ = p⁻¹ := hconj
      _ = (u * v')⁻¹ := by rw [← hpuv]
      _ = v'⁻¹ * u⁻¹ := by rw [mul_inv_rev]
      _ = u⁻¹ * v'⁻¹ := hcomm_inv
  obtain ⟨hu_inv, hv'_inv⟩ := h.unique (hgU u hu) (U.inv_mem hu) hgv'
    ((conjSub t U).inv_mem hv') hconj'
  have hv_eq : g * v * g⁻¹ = v⁻¹ := by
    have h : t * (g * v * g⁻¹) * t⁻¹ = t * v⁻¹ * t⁻¹ := by
      have h := hv'_inv
      rw [hv'eq, conj_conjSub_eq htg,
        show (t * v * t⁻¹)⁻¹ = t * v⁻¹ * t⁻¹ from by group] at h
      exact h
    calc g * v * g⁻¹ = t⁻¹ * (t * (g * v * g⁻¹) * t⁻¹) * t := by group
      _ = t⁻¹ * (t * v⁻¹ * t⁻¹) * t := by rw [h]
      _ = v⁻¹ := by group
  have huFU : u ∈ FU := hFU_inv u hu hu_inv
  have hvFU : v ∈ FU := hFU_inv v hv hv_eq
  have hBle : conjSub t FU ≤ conjSub t U := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t FU b).mp hb
    exact (mem_conjSub_iff' t U _).mpr ⟨w, hFU_le hw, rfl⟩
  have hv'mem : t * v * t⁻¹ ∈ conjSub t FU :=
    (mem_conjSub_iff' t FU _).mpr ⟨v, hvFU, rfl⟩
  have hA : IsElemAbelian 2 FU := hFU_el
  have hB : IsElemAbelian 2 (conjSub t FU) := by
    rw [conjSub]
    exact hFU_el.map (MulAut.conj t).toMonoidHom
  have hcommAB : ∀ a ∈ FU, ∀ b ∈ conjSub t FU, a * b = b * a :=
    fun a ha b hb => h.direct.2.2 a (hFU_le ha) b (hBle hb)
  have hAB : IsElemAbelian 2 (FU ⊔ conjSub t FU) := hA.sup_of_commute hB hcommAB
  have hFUg : ∀ w ∈ FU, w * g = g * w := by
    intro w hw
    have hwg : g * w = w * g := by
      calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [hFU_cent w hw]
    exact hwg.symm
  have hBg : ∀ b ∈ conjSub t FU, b * g = g * b := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := (mem_conjSub_iff' t FU b).mp hb
    exact (conj_comm_zpowers htg (hFUg w hw).symm).symm
  have hABg_mem : FU ⊔ conjSub t FU ≤ Subgroup.centralizer ({g} : Set G) :=
    sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hFUg w hw))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hBg b hb))
  have hcommZ : ∀ a ∈ FU ⊔ conjSub t FU, ∀ z ∈ zpowers g, a * z = z * a := by
    intro a ha z hz
    have haC : a ∈ Subgroup.centralizer (zpowers g : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hABg_mem ha
    exact (Subgroup.mem_centralizer_iff.mp haC z hz).symm
  have hABZ : IsElemAbelian 2 ((FU ⊔ conjSub t FU) ⊔ zpowers g) :=
    hAB.sup_of_commute (isElemAbelian_zpowers hF.g_sq) hcommZ
  have hdisj : Disjoint FU (conjSub t FU) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro a ha
    rw [Subgroup.mem_bot]
    have hmem : a ∈ U ⊓ conjSub t U := ⟨hFU_le ha.1, hBle ha.2⟩
    rw [h.direct.2.1, Subgroup.mem_bot] at hmem
    exact hmem
  have hcentAB : conjSub t FU ≤ Subgroup.centralizer (FU : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.direct.2.2 a (hFU_le ha) b (hBle hb)
  have hnorm : conjSub t FU ≤ Subgroup.normalizer (FU : Set G) :=
    hcentAB.trans (Subgroup.centralizer_le_normalizer (FU : Set G))
  have hcardB : Nat.card (conjSub t FU) = 8 := by
    rw [conjSub]
    rw [Subgroup.card_map_of_injective (K := FU) (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective, hFU_card]
  have hcardAB : Nat.card (FU ⊔ conjSub t FU : Subgroup G) = 64 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer FU (conjSub t FU)
      hnorm hdisj, hFU_card, hcardB]
  have hcardE : 64 ≤ Nat.card ((FU ⊔ conjSub t FU) ⊔ zpowers g : Subgroup G) := by
    have hle : FU ⊔ conjSub t FU ≤ (FU ⊔ conjSub t FU) ⊔ zpowers g := le_sup_left
    have hcard := Subgroup.card_le_of_le hle
    rwa [hcardAB] at hcard
  have hE_le : ((FU ⊔ conjSub t FU) ⊔ zpowers g) ≤ P ⊔ zpowers g := by
    refine sup_le ?_ le_sup_right
    refine sup_le ?_ ?_
    · exact hFU_le.trans (h.le_left.1.trans le_sup_left)
    · exact hBle.trans (h.le_left.2.trans le_sup_left)
  have hu_mem : u ∈ (FU ⊔ conjSub t FU) ⊔ zpowers g :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left huFU)
  have hv'_mem : t * v * t⁻¹ ∈ (FU ⊔ conjSub t FU) ⊔ zpowers g :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right hv'mem)
  have hg_mem : g ∈ (FU ⊔ conjSub t FU) ⊔ zpowers g :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hpg_mem : p * g ∈ (FU ⊔ conjSub t FU) ⊔ zpowers g := by
    rw [hpuv, hv'eq]
    have h1 : u * (t * v * t⁻¹) ∈ (FU ⊔ conjSub t FU) ⊔ zpowers g :=
      (((FU ⊔ conjSub t FU) ⊔ zpowers g).mul_mem hu_mem hv'_mem)
    exact ((FU ⊔ conjSub t FU) ⊔ zpowers g).mul_mem h1 hg_mem
  exact ⟨(FU ⊔ conjSub t FU) ⊔ zpowers g, hE_le, hABZ, hcardE, hpg_mem⟩

theorem y7n_case2_cover (h : Wr7 t P U) (hS : centEl P t = S) (hF : SgFacts S F g)
    (htg : t * g = g * t) (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U) : ElemCover 64 (P ⊔ zpowers g) := by
  intro x hx hx2
  have hgP : ∀ y ∈ P, g * y * g⁻¹ ∈ P :=
    fun y hy => Wr7.conj_mem_of_normalizes h htg hgU hy
  rcases y7n_mem_sup_zpowers hF.g_sq hgP hx with hxP | ⟨y, hy, hxy⟩
  · have hRankU : RankFacts U :=
      RankFacts.of_mulEquiv h.centEquiv.symm (RankFacts.of_eq hS.symm hF.rank)
    have hUcover : ElemCover 8 U := RankFacts.elemCover hRankU
    have hU'cover : ElemCover 8 (conjSub t U) := ElemCover.conj t hUcover
    have hPcover : ElemCover 64 P := by
      have h88 : ElemCover (8 * 8) P := ElemCover.prod h.direct hUcover hU'cover
      simpa only [show (8 : ℕ) * 8 = 64 by norm_num] using h88
    obtain ⟨E, hEP, hEel, hEcard, hxE⟩ := hPcover x hxP hx2
    exact ⟨E, hEP.trans le_sup_left, hEel, hEcard, hxE⟩
  · have hy2 : (y * g) ^ 2 = 1 := by rw [← hxy]; exact hx2
    obtain ⟨E, hE_le, hEel, hEcard, hyE⟩ := y7n_coset_cover h hS hF htg hgU y hy hy2
    exact ⟨E, hE_le, hEel, hEcard, by rw [hxy]; exact hyE⟩

end CFSG.OddStandard.HigherRank.YamadaG23
