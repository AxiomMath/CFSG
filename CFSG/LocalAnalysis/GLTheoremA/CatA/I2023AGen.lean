module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Normalizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev rho (L : Subgroup G) : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (PQuot 3 L) :=
  CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L

theorem rho_mk' (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (y y' : ↥L)
    (h : (y' : G) = g * y * g⁻¹) :
    rho L ⟨g, hg⟩ (QuotientGroup.mk y) = QuotientGroup.mk y' := by
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
  congr 1
  apply Subtype.ext
  rw [h]
  rfl

theorem mem_core_iff {p : ℕ} {L : Subgroup G} (x : ↥L) :
    (x : G) ∈ GLAPPrimeCoreOf p L ↔ x ∈ GLAPPrimeCore p ↥L :=
  ⟨fun ⟨c', hc', hv⟩ => by
    have : c' = x := Subtype.ext hv
    rwa [this] at hc', fun h => ⟨x, h, rfl⟩⟩

theorem mk_eq_iff (L : Subgroup G) (y z : ↥L) :
    (QuotientGroup.mk y : PQuot 3 L) = QuotientGroup.mk z ↔
      (y : G)⁻¹ * (z : G) ∈ GLAPPrimeCoreOf 3 L := by
  rw [QuotientGroup.eq, ← mem_core_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem rho_eq_one_iff (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    rho L ⟨g, hg⟩ = 1 ↔ g ∈ centModSubgroup 3 L := by
  constructor
  · intro h
    refine ⟨hg, fun l hl => ?_⟩
    have hl' : l⁻¹ ∈ L := L.inv_mem hl
    have h1 := congrArg (fun φ : MulAut (PQuot 3 L) => φ (QuotientGroup.mk ⟨l⁻¹, hl'⟩)) h
    simp only [MulAut.one_apply] at h1
    have hy : g * l⁻¹ * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg l⁻¹).1 hl'
    rw [rho_mk' L hg ⟨l⁻¹, hl'⟩ ⟨g * l⁻¹ * g⁻¹, hy⟩ rfl] at h1
    have h2 := (mk_eq_iff L _ _).1 h1.symm
    have e : ⁅l, g⁆ = (l⁻¹)⁻¹ * (g * l⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact h2
  · intro h
    apply MulEquiv.ext
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : g * (y : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg (y : G)).1 y.2
    rw [rho_mk' L hg y ⟨g * y * g⁻¹, hy⟩ rfl, MulAut.one_apply]
    symm
    rw [mk_eq_iff]
    have := h.2 (y : G)⁻¹ (L.inv_mem y.2)
    have e : ⁅(y : G)⁻¹, g⁆ = (y : G)⁻¹ * (g * y * g⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e] at this
    exact this

theorem rho_inner (L : Subgroup G) (l : ↥L) :
    rho L ⟨(l : G), Subgroup.le_normalizer l.2⟩ = MulAut.conj (QuotientGroup.mk l : PQuot 3 L) := by
  apply MulEquiv.ext
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [rho_mk' L (Subgroup.le_normalizer l.2) y (l * y * l⁻¹) (by simp), MulAut.conj_apply]
  rfl

theorem isElemAbelian_closure {M : Type*} [Group M] (s : Set M)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (h3 : ∀ a ∈ s, a ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.closure s) := by
  have h1 : ∀ b ∈ Subgroup.closure s, ∀ a ∈ s, a * b = b * a := by
    intro b hb a ha
    have : Subgroup.closure s ≤ Subgroup.centralizer ({a} : Set M) := by
      rw [Subgroup.closure_le]
      intro c hcs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hc a ha c hcs).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this hb)).symm
  have hcomm : ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, a * b = b * a := by
    intro a ha b hb
    have : Subgroup.closure s ≤ Subgroup.centralizer ({b} : Set M) := by
      rw [Subgroup.closure_le]
      intro c hcs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h1 b hb c hcs
    exact Subgroup.mem_centralizer_singleton_iff.1 (this ha)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem a ha => exact h3 a ha
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    rw [(show Commute a b from hcomm a ha b hb).mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem isElemAbelian_map_inj {H M : Type*} [Group H] [Group M] (f : H →* M)
    (hf : Function.Injective f) {S₀ : Subgroup H} (h : IsElemAbelian 3 S₀) :
    IsElemAbelian 3 (S₀.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨a₀, ha₀, ha⟩ := a.2
    obtain ⟨b₀, hb₀, hb⟩ := b.2
    apply Subtype.ext
    show (a : M) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg (fun z : ↥S₀ => (z : H)) (h.1.is_comm.comm ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩)
  · obtain ⟨s, hs, rfl⟩ := hg
    rw [← map_pow, h.2 s hs, map_one]

theorem mk_eq_iff_X (X : Subgroup G) (y z : ↥X) :
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) z ↔
      (y : G)⁻¹ * (z : G) ∈ GLAPPrimeCoreOf 3 X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← mem_core_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem glaPPrimeCoreOf_le_centMod {X L : Subgroup G} (hL : GLAPComponent 3 X L) :
    GLAPPrimeCoreOf 3 X ≤ centModSubgroup 3 L := by
  intro n hn
  have hnL : n ∈ Subgroup.normalizer (L : Set G) :=
    glaPPrimeCoreOf_le_normalizer_of_component hL hn
  refine ⟨hnL, fun l hl => ?_⟩
  have hlX : l ∈ X := hL.1 hl
  have h1 : ⁅l, n⁆ ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.1 hnL l⁻¹).1 (L.inv_mem hl)
    have e : ⁅l, n⁆ = l * (n * l⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem hl h
  have h2 : ⁅l, n⁆ ∈ GLAPPrimeCoreOf 3 X := by
    have h := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 X hlX) n).1 hn
    have e : ⁅l, n⁆ = (l * n * l⁻¹) * n⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hn)
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hL.2.1]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem rho_of_mem_core {X L : Subgroup G} (hL : GLAPComponent 3 X L) {n : G}
    (hn : n ∈ GLAPPrimeCoreOf 3 X) (hnN : n ∈ Subgroup.normalizer (L : Set G)) :
    rho L ⟨n, hnN⟩ = 1 :=
  (rho_eq_one_iff L hnN).2 (glaPPrimeCoreOf_le_centMod hL hn)

theorem rho_eq_of_inv_mul_mem {X L : Subgroup G} (hL : GLAPComponent 3 X L) {p s : G}
    (hp : p ∈ Subgroup.normalizer (L : Set G)) (hs : s ∈ Subgroup.normalizer (L : Set G))
    (h : p⁻¹ * s ∈ GLAPPrimeCoreOf 3 X) : rho L ⟨s, hs⟩ = rho L ⟨p, hp⟩ := by
  have hn : p⁻¹ * s ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hp) hs
  have h1 := rho_of_mem_core hL h hn
  have e : (⟨s, hs⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨p, hp⟩ * ⟨p⁻¹ * s, hn⟩ :=
    Subtype.ext (by simp)
  rw [e, map_mul, h1, mul_one]

theorem sstar_layer_three {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax 3 B x L) :
    GLAPLayer 3 (cx x) = L := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hS := S10.sstar_triple h
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hLc : GLAPComponent 3 (cx x) L := hS.2.2
  have hxp : x ^ 3 = 1 := hS.1.1.2 x hxB
  have hxL : x ∈ centModSubgroup 3 L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc.1 hl)
  apply le_antisymm
  · refine sSup_le fun J hJ => ?_
    by_cases hJL : J = L
    · exact hJL ▸ le_rfl
    exfalso
    have hJCm : J ≤ centModSubgroup 3 L := le_centModSubgroup_of_ne hp hJ hLc hJL
    obtain ⟨w, hwJ, hwp, k, hkJ, hkw⟩ := exists_pow_eq_one_noncomm_of_component hp hp2 hJ
    have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hkJ)
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hwJ)
    have hwnx : w ∉ Subgroup.zpowers x := by
      intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact hkw (hkx.zpow_right n).eq
    obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hwx hwp hxp hx1 hwnx
    have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x ≤ centModSubgroup 3 L :=
      sup_le (Subgroup.zpowers_le.2 (hJCm hwJ)) (Subgroup.zpowers_le.2 hxL)
    have hcycS : IsCyclic (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) :=
      h.2 (Subgroup.zpowers w ⊔ Subgroup.zpowers x)
        (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
    have hdiv : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) ≤ 3 :=
      card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
    rw [hcard] at hdiv
    omega
  · exact le_sSup hLc

theorem cx_le_normalizer {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax 3 B x L) :
    cx x ≤ Subgroup.normalizer (L : Set G) := fun g hg => by
  rw [← sstar_layer_three h]
  exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
