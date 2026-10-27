module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ThreeOutRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

theorem mem_of_central_pow {p : ℕ} (hp : p.Prime) {Z : Type*} [Group Z] [Finite Z]
    {L P : Subgroup Z} (hPL : P ≤ L) (hPp : IsPGroup p P)
    (hPidx : ¬ p ∣ (P.subgroupOf L).index) {c : Z} (hcL : c ∈ L)
    (hcc : ∀ l ∈ L, l * c = c * l) (hcp : c ^ p = 1) : c ∈ P := by
  haveI := Fact.mk hp
  have hQ : IsPGroup p (P.subgroupOf L) := hPp.comap_subtype
  let c' : L := ⟨c, hcL⟩
  have hc'p : c' ^ p = 1 := Subtype.ext hcp
  have hc'cen : c' ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcc g.1 g.2)
  haveI : (Subgroup.zpowers c').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc'cen)
  have hN : IsPGroup p (Subgroup.zpowers c') := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hc'p) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hNS : Subgroup.zpowers c' ≤ (hQ.toSylow hPidx).toSubgroup :=
    IsPGroup.le_sylow_of_normal hN (hQ.toSylow hPidx)
  have hmem : c' ∈ P.subgroupOf L := hNS (Subgroup.mem_zpowers c')
  exact Subgroup.mem_subgroupOf.mp hmem

theorem conj_mem_sup_zpowers_of_gen {Z : Type*} [Group Z] {e c k h : Z}
    (h1 : k * e * k⁻¹ ∈ zpowers e ⊔ zpowers c) (h2 : k * c * k⁻¹ ∈ zpowers e ⊔ zpowers c)
    (hh : h ∈ zpowers e ⊔ zpowers c) : k * h * k⁻¹ ∈ zpowers e ⊔ zpowers c := by
  have hT : zpowers e ⊔ zpowers c ≤ (zpowers e ⊔ zpowers c).comap (MulAut.conj k).toMonoidHom :=
    sup_le (zpowers_le.2 h1) (zpowers_le.2 h2)
  exact hT hh

theorem mem_normalizer_sup_zpowers {Z : Type*} [Group Z] {e c g : Z}
    (h1 : g * e * g⁻¹ ∈ zpowers e ⊔ zpowers c) (h2 : g * c * g⁻¹ ∈ zpowers e ⊔ zpowers c)
    (h3 : g⁻¹ * e * g ∈ zpowers e ⊔ zpowers c) (h4 : g⁻¹ * c * g ∈ zpowers e ⊔ zpowers c) :
    g ∈ normalizer ((zpowers e ⊔ zpowers c : Subgroup Z) : Set Z) := by
  have h3' : g⁻¹ * e * g⁻¹⁻¹ ∈ zpowers e ⊔ zpowers c := by
    rw [inv_inv]
    exact h3
  have h4' : g⁻¹ * c * g⁻¹⁻¹ ∈ zpowers e ⊔ zpowers c := by
    rw [inv_inv]
    exact h4
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe]
  constructor
  · intro hh
    exact conj_mem_sup_zpowers_of_gen h1 h2 hh
  · intro hh
    have h' := conj_mem_sup_zpowers_of_gen h3' h4' hh
    have key : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [key] at h'

theorem lift_mem_Y {p : ℕ} (hp : p.Prime) {Z : Type*} [Group Z] [Finite Z]
    (L P E₀ Y ZL : Subgroup Z) (hPL : P ≤ L) (hPp : IsPGroup p P)
    (hPidx : ¬ p ∣ (P.subgroupOf L).index) (hE₀P : E₀ ≤ P) (hE₀ : IsElemAbelian p E₀)
    (hZLL : ZL ≤ L) (hZLc : ∀ l ∈ L, ∀ z ∈ ZL, l * z = z * l)
    (h2 : ∀ S : Subgroup Z, S ≤ P → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (h1 : ∀ S : Subgroup Z, S ≤ E₀ → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    {e g : Z} (he : e ∈ E₀) (heZ : e ∉ ZL) (hg : g ∈ L) (hc : g * e * g⁻¹ * e⁻¹ ∈ ZL) :
    g ∈ Y := by
  haveI := Fact.mk hp
  have hep : e ^ p = 1 := hE₀.2 e he
  have heL : e ∈ L := hPL (hE₀P he)
  have he1 : e ≠ 1 := fun h => heZ (h ▸ ZL.one_mem)
  have hord : orderOf e = p := orderOf_eq_prime hep he1
  set c : Z := g * e * g⁻¹ * e⁻¹ with hcdef
  have hcZL : c ∈ ZL := hc
  have hge : g * e * g⁻¹ = c * e := by simp [hcdef]
  have hcc : ∀ l ∈ L, l * c = c * l := fun l hl => hZLc l hl c hcZL
  have hcp : c ^ p = 1 := by
    have h1' : (g * e * g⁻¹) ^ p = 1 := by
      rw [conj_pow, hep]
      simp
    rw [hge] at h1'
    have hcomm : Commute c e := (hcc e heL).symm
    rwa [hcomm.mul_pow, hep, mul_one] at h1'
  by_cases hc1 : c = 1
  ·
    have hgE : Commute g e := by
      have : g * e * g⁻¹ = e := by rw [hge, hc1, one_mul]
      exact mul_inv_eq_iff_eq_mul.1 this
    have hE : zpowers e ≤ E₀ := zpowers_le.2 he
    have hrk : 1 ≤ Open.pRank p (zpowers e) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers hep) (k := 1)
        (by rw [Nat.card_zpowers, hord]; simp)
    apply h1 _ hE hrk
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨n, rfl⟩
    exact (hgE.zpow_right n).eq.symm
  · have hcP : c ∈ P := mem_of_central_pow hp hPL hPp hPidx (hZLL hcZL) hcc hcp
    have hdisj : e ∉ zpowers c := fun h => heZ (zpowers_le.2 hcZL h)
    have hS := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hcp hep hc1 hdisj
      (hcc e heL).symm
    rw [sup_comm] at hS
    have hSP : zpowers e ⊔ zpowers c ≤ P :=
      sup_le (zpowers_le.2 (hE₀P he)) (zpowers_le.2 hcP)
    have hrk : 2 ≤ Open.pRank p (zpowers e ⊔ zpowers c) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hS.1 (k := 2) hS.2
    have heS : e ∈ zpowers e ⊔ zpowers c := le_sup_left (a := zpowers e) (mem_zpowers e)
    have hcS : c ∈ zpowers e ⊔ zpowers c := le_sup_right (b := zpowers c) (mem_zpowers c)
    have hgc : g * c * g⁻¹ = c := by
      rw [hcc g hg]; simp
    have hgic : g⁻¹ * c * g = c := by
      rw [hcc g⁻¹ (inv_mem hg)]; simp
    have hgie : g⁻¹ * e * g = c⁻¹ * e := by
      have h3 : e = c * (g⁻¹ * e * g) := by
        have : g⁻¹ * (c * e) * g = e := by rw [← hge]; group
        calc e = g⁻¹ * (c * e) * g := this.symm
          _ = c * (g⁻¹ * e * g) := by
            have hc' : g⁻¹ * c = c * g⁻¹ := hcc g⁻¹ (inv_mem hg)
            calc g⁻¹ * (c * e) * g = (g⁻¹ * c) * e * g := by group
              _ = (c * g⁻¹) * e * g := by rw [hc']
              _ = c * (g⁻¹ * e * g) := by group
      calc g⁻¹ * e * g = c⁻¹ * (c * (g⁻¹ * e * g)) := by group
        _ = c⁻¹ * e := by rw [← h3]
    have hgn : g ∈ normalizer ((zpowers e ⊔ zpowers c : Subgroup Z) : Set Z) :=
      mem_normalizer_sup_zpowers (by rw [hge]; exact mul_mem hcS heS) (by rw [hgc]; exact hcS)
        (by rw [hgie]; exact mul_mem (inv_mem hcS) heS) (by rw [hgic]; exact hcS)
    exact h2 _ hSP hrk hgn

theorem plane_or_central {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (hE : IsElemAbelian p E) (hE3 : Nat.card E = p ^ 3) (N : Subgroup G)
    [N.Normal] :
    (∃ S : Subgroup G, S ≤ E ∧ S ≤ N ∧ IsElemAbelian p S ∧ Nat.card S = p ^ 2) ∨
    (∃ D : Subgroup (G ⧸ N), IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
      D ≤ E.map (QuotientGroup.mk' N)) := by
  haveI := Fact.mk hp
  have hC : IsElemAbelian p (N ⊓ E) := hE.mono inf_le_right
  have hdvd : Nat.card (N ⊓ E : Subgroup G) ∣ p ^ 3 := by
    rw [← hE3]
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨j, -, hCj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  ·
    right
    have hψker : ((QuotientGroup.mk' N).comp E.subtype).ker = N.subgroupOf E := by
      ext x
      simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hcardC := Subgroup.card_map_of_injective (K := N.subgroupOf E) E.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at hcardC
    have hker : Nat.card ((QuotientGroup.mk' N).comp E.subtype).ker ∣ p := by
      rw [hψker, ← hcardC, hCj]
      have h1 : p ^ j ∣ p ^ 1 := pow_dvd_pow p (by omega)
      rwa [pow_one] at h1
    have hrange : ((QuotientGroup.mk' N).comp E.subtype).range = E.map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hQ : Nat.card E = p ^ (2 + 1) := hE3.trans (by norm_num)
    have hdvd2 : p ^ 2 ∣ Nat.card ((QuotientGroup.mk' N).comp E.subtype).range :=
      CFSG.HardMathSupport.Dickson.I271.ThreeOutRank.pow_dvd_card_range hQ _ hker
    rw [hrange] at hdvd2
    obtain ⟨D, hDA, hD, hDc⟩ :=
      CFSG.HardMathSupport.Dickson.I271.ThreeOutRank.exists_isElemAbelian_card
        (hE.map (QuotientGroup.mk' N)) hdvd2
    exact ⟨D, hD, hDc, hDA⟩
  ·
    left
    have hdvd2 : p ^ 2 ∣ Nat.card (N ⊓ E : Subgroup G) := by
      rw [hCj]
      exact pow_dvd_pow p hj2
    obtain ⟨D, hDC, hD, hDc⟩ :=
      CFSG.HardMathSupport.Dickson.I271.ThreeOutRank.exists_isElemAbelian_card hC hdvd2
    exact ⟨D, hDC.trans inf_le_right, hDC.trans inf_le_left, hD, hDc⟩

theorem commElt_mul_central_left {G : Type*} [Group G] {z : G} (hz : ∀ g : G, g * z = z * g)
    (a b : G) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b * z⁻¹ = b := by rw [← hz b, mul_inv_cancel_right]
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [hzb, commutatorElement_def]

theorem commElt_mul_central_right {G : Type*} [Group G] {z : G} (hz : ∀ g : G, g * z = z * g)
    (a b : G) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ * z⁻¹ = a⁻¹ := by rw [← hz a⁻¹, mul_inv_cancel_right]
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [hza, commutatorElement_def]

theorem commElt_mul_central {G : Type*} [Group G] {z₁ z₂ : G}
    (hz₁ : ∀ g : G, g * z₁ = z₁ * g) (hz₂ : ∀ g : G, g * z₂ = z₂ * g) (a b : G) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commElt_mul_central_left hz₁, commElt_mul_central_right hz₂]

theorem le_of_plane_generation {p : ℕ} (hp : p.Prime) {Z : Type*} [Group Z] [Finite Z]
    (L P E₀ Y : Subgroup Z) (hLperf : commutator ↥L = ⊤) (hPL : P ≤ L) (hPp : IsPGroup p P)
    (hPidx : ¬ p ∣ (P.subgroupOf L).index) (hE₀P : E₀ ≤ P) (hE₀ : IsElemAbelian p E₀)
    (hE₀c : Nat.card E₀ = p ^ 3)
    (h2 : ∀ S : Subgroup Z, S ≤ P → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (h1 : ∀ S : Subgroup Z, S ≤ E₀ → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hSeitz : ∀ D : Subgroup (↥L ⧸ center ↥L), IsElemAbelian p D → Nat.card D = p ^ 2 →
      Subgroup.closure {k : ↥L ⧸ center ↥L | ∃ d ∈ D, d ≠ 1 ∧ k * d = d * k} = ⊤) :
    L ≤ Y := by
  have hp1 : 1 < p := hp.one_lt
  have hE₀L : E₀ ≤ L := hE₀P.trans hPL
  have hZLL : (center ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le (center ↥L)
  have hZLc : ∀ l ∈ L, ∀ z ∈ (center ↥L).map L.subtype, l * z = z * l := by
    intro l hl z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    have h := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨l, hl⟩)
    simpa using h
  have hE'ab : IsElemAbelian p (E₀.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hE₀ L
  have hE'c : Nat.card (E₀.subgroupOf L) = p ^ 3 := by
    have h := Subgroup.card_map_of_injective (K := E₀.subgroupOf L) L.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE₀L, hE₀c] at h
    exact h.symm
  rcases plane_or_central hp (E₀.subgroupOf L) hE'ab hE'c (center ↥L) with
    ⟨S, hSE', hSZ, hSab, hScard⟩ | ⟨D, hDab, hDcard, hDle⟩
  ·
    have hS₀ab : IsElemAbelian p (S.map L.subtype) :=
      CFSG.Open.IsElemAbelian.map hSab L.subtype
    have hS₀c : Nat.card (S.map L.subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hScard
    have hS₀P : S.map L.subtype ≤ P := by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
      exact hE₀P (Subgroup.mem_subgroupOf.mp (hSE' hs))
    have hrank : 2 ≤ Open.pRank p (S.map L.subtype) :=
      CFSG.SectionRank.le_pRank hp1 le_rfl hS₀ab hS₀c
    have hcomm : ∀ g ∈ L, ∀ z ∈ S.map L.subtype, g * z = z * g := by
      intro g hg z hz
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
      have h := congrArg Subtype.val ((Subgroup.mem_center_iff.mp (hSZ hs)) ⟨g, hg⟩)
      simpa using h
    have hLnorm : L ≤ normalizer ((S.map L.subtype : Subgroup Z) : Set Z) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hh' : h ∈ S.map L.subtype := hh
        rw [hcomm g hg h hh', mul_inv_cancel_right]
        exact hh
      · intro hh
        have hc := hcomm g⁻¹ (L.inv_mem hg) (g * h * g⁻¹) hh
        have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [e, hc, inv_mul_cancel_right]
        exact hh
    exact hLnorm.trans (h2 _ hS₀P hrank)
  ·
    have hWle : Subgroup.closure {k : ↥L ⧸ center ↥L | ∃ d ∈ D, d ≠ 1 ∧ k * d = d * k} ≤
        (Y.comap L.subtype).map (QuotientGroup.mk' (center ↥L)) := by
      rw [Subgroup.closure_le]
      rintro k ⟨d, hdD, hd1, hkd⟩
      obtain ⟨e', he'E, hde⟩ := Subgroup.mem_map.mp (hDle hdD)
      subst hde
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center ↥L) k
      have hcen : g * e' * g⁻¹ * e'⁻¹ ∈ center ↥L := by
        have h1' : QuotientGroup.mk' (center ↥L) (g * e' * g⁻¹ * e'⁻¹) =
            (1 : ↥L ⧸ center ↥L) := by
          simp only [map_mul, map_inv]
          rw [hkd]
          group
        exact (QuotientGroup.eq_one_iff (g * e' * g⁻¹ * e'⁻¹)).mp h1'
      have heZ : (e' : Z) ∉ (center ↥L).map L.subtype := by
        intro hmem
        obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hmem
        have hce' : c = e' := Subtype.ext hce
        rw [hce'] at hc
        exact hd1 ((QuotientGroup.eq_one_iff e').mpr hc)
      have hc : (g : Z) * (e' : Z) * (g : Z)⁻¹ * (e' : Z)⁻¹ ∈ (center ↥L).map L.subtype :=
        Subgroup.mem_map_of_mem L.subtype hcen
      have hY : (g : Z) ∈ Y :=
        lift_mem_Y hp L P E₀ Y ((center ↥L).map L.subtype) hPL hPp hPidx hE₀P hE₀ hZLL hZLc
          h2 h1 (Subgroup.mem_subgroupOf.mp he'E) heZ g.2 hc
      exact Subgroup.mem_map_of_mem _ hY
    rw [hSeitz D hDab hDcard] at hWle
    have hcov : ∀ x : ↥L, ∃ w : ↥L, w ∈ Y.comap L.subtype ∧ w⁻¹ * x ∈ center ↥L := by
      intro x
      obtain ⟨w, hw, hwx⟩ :=
        Subgroup.mem_map.mp (hWle (Subgroup.mem_top (QuotientGroup.mk' (center ↥L) x)))
      refine ⟨w, hw, ?_⟩
      have hwx' : (w : ↥L ⧸ center ↥L) = (x : ↥L ⧸ center ↥L) := hwx
      exact QuotientGroup.eq.mp hwx'
    have hcomm_W : commutator ↥L ≤ Y.comap L.subtype := by
      show ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ Y.comap L.subtype
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨w1, hw1, hz1⟩ := hcov x
      obtain ⟨w2, hw2, hz2⟩ := hcov y
      have hxy : ⁅x, y⁆ = ⁅w1, w2⁆ := by
        have h := commElt_mul_central (Subgroup.mem_center_iff.mp hz1)
          (Subgroup.mem_center_iff.mp hz2) w1 w2
        rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
      rw [hxy, commutatorElement_def]
      exact (Y.comap L.subtype).mul_mem
        ((Y.comap L.subtype).mul_mem ((Y.comap L.subtype).mul_mem hw1 hw2)
          ((Y.comap L.subtype).inv_mem hw1))
        ((Y.comap L.subtype).inv_mem hw2)
    have hW : (⊤ : Subgroup ↥L) ≤ Y.comap L.subtype := by
      have h := hcomm_W
      rw [hLperf] at h
      exact h
    intro l hl
    exact Subgroup.mem_comap.mp (hW (Subgroup.mem_top (⟨l, hl⟩ : ↥L)))

@[expose] def SeitzGen (p : ℕ) (Q : Type*) [Group Q] : Prop :=
  ∀ D : Subgroup Q, IsElemAbelian p D → Nat.card D = p ^ 2 →
    Subgroup.closure {k : Q | ∃ d ∈ D, d ≠ 1 ∧ k * d = d * k} = ⊤

theorem le_of_seitzGen {p : ℕ} (hp : p.Prime) {Z : Type*} [Group Z] [Finite Z]
    (L P Y : Subgroup Z) (hLq : Open.IsQuasisimple ↥L) (hPL : P ≤ L) (hPp : IsPGroup p P)
    (hPidx : ¬ p ∣ (P.subgroupOf L).index) (hrk : 3 ≤ Open.pRank p P)
    (hSG : SeitzGen p (↥L ⧸ center ↥L))
    (hY2 : ∀ S : Subgroup Z, S ≤ P → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hY1 : ∀ E : Subgroup Z, E ≤ P → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) :
    L ≤ Y := by
  haveI := Fact.mk hp
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt P
  have h3 : p ^ 3 ∣ Nat.card E := by
    rw [hEc]
    exact pow_dvd_pow p hrk
  haveI : Finite E := inferInstance
  obtain ⟨E₀, hE₀E, hE₀, hE₀c⟩ :=
    CFSG.HardMathSupport.Dickson.I271.ThreeOutRank.exists_isElemAbelian_card hE h3
  have hE₀P : E₀ ≤ P := hE₀E.trans hEP
  exact le_of_plane_generation hp L P E₀ Y hLq.1 hPL hPp hPidx hE₀P hE₀ hE₀c hY2
    (fun S hS hr => hY1 E₀ hE₀P hE₀ hE₀c S hS hr) hSG

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
