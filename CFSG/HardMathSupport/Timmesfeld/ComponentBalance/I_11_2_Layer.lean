module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_LayerCore
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_LayerTransport
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartI
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists
import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

section Algebra

theorem dvd_index_center {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple L) (hpL : p ∣ Nat.card L)
    (hZ : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = p) :
    p ∣ (Subgroup.center L).index := by
  rcases hZ with h | h
  · have := Subgroup.card_mul_index (Subgroup.center L)
    rw [h, one_mul] at this
    rwa [← this] at hpL
  · by_contra hnd
    have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) (Subgroup.center L).index := by
      rw [h]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
    have hcomm : commutator L ≤ H := by
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      obtain ⟨⟨⟨z, hz⟩, ⟨h1, hh1⟩⟩, rfl⟩ := hH.2 a
      obtain ⟨⟨⟨z', hz'⟩, ⟨h2, hh2⟩⟩, rfl⟩ := hH.2 b
      have hzc : ∀ w : L, z * w * z⁻¹ = w := fun w => by
        rw [← Subgroup.mem_center_iff.1 hz w]; group
      have hzc' : ∀ w : L, z' * w * z'⁻¹ = w := fun w => by
        rw [← Subgroup.mem_center_iff.1 hz' w]; group
      simp only
      rw [commutatorElement_def]
      have e1 : z * h1 * (z' * h2) * (z * h1)⁻¹ * (z' * h2)⁻¹ =
          (h1 * (z' * h2) * h1⁻¹) * (z' * h2)⁻¹ := by
        calc z * h1 * (z' * h2) * (z * h1)⁻¹ * (z' * h2)⁻¹
            = (z * (h1 * (z' * h2) * h1⁻¹) * z⁻¹) * (z' * h2)⁻¹ := by group
          _ = (h1 * (z' * h2) * h1⁻¹) * (z' * h2)⁻¹ := by rw [hzc]
      have hzh : h1 * z' = z' * h1 := Subgroup.mem_center_iff.1 hz' h1
      have e2 : h1 * (z' * h2) * h1⁻¹ * (z' * h2)⁻¹ = h1 * h2 * h1⁻¹ * h2⁻¹ := by
        calc h1 * (z' * h2) * h1⁻¹ * (z' * h2)⁻¹
            = (h1 * z') * h2 * h1⁻¹ * h2⁻¹ * z'⁻¹ := by group
          _ = (z' * h1) * h2 * h1⁻¹ * h2⁻¹ * z'⁻¹ := by rw [hzh]
          _ = z' * (h1 * h2 * h1⁻¹ * h2⁻¹) * z'⁻¹ := by group
          _ = h1 * h2 * h1⁻¹ * h2⁻¹ := hzc' _
      rw [e1, e2]
      exact H.mul_mem (H.mul_mem (H.mul_mem hh1 hh2) (H.inv_mem hh1)) (H.inv_mem hh2)
    have hHtop : H = ⊤ := by
      rw [eq_top_iff, ← hq.1]; exact hcomm
    have hbot : Subgroup.center L = ⊥ :=
      hH.disjoint.eq_bot_of_le (hHtop ▸ le_top)
    rw [hbot, Subgroup.card_bot] at h
    exact hp.one_lt.ne h

end Algebra

section Setup

variable {X : Type*} [Group X]

theorem mem_of_zpow_mem {p : ℕ} (hp : p.Prime) {b : X} (hb : b ^ p = 1) {H : Subgroup X}
    {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (h : b ^ a ∈ H) : b ∈ H := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : (a : ZMod p) ≠ 0 := fun h0 => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 h0)
  set t : ℤ := (((a : ZMod p)⁻¹).val : ℤ) with ht
  have hcast : ((a * t - 1 : ℤ) : ZMod p) = 0 := by
    have : ((t : ℤ) : ZMod p) = (a : ZMod p)⁻¹ := by
      rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast
    rw [this, mul_inv_cancel₀ hne, sub_self]
  obtain ⟨s, hs⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hcast
  have hat : a * t = 1 + p * s := by linarith
  have : b = (b ^ a) ^ t := by
    rw [← zpow_mul, hat, zpow_add, zpow_one, zpow_mul, zpow_natCast, hb, one_zpow, mul_one]
  rw [this]
  exact H.zpow_mem h t

theorem lbp_add {p : ℕ} [NeZero p] {b : X} (hb : b ^ p = 1) (k k' : ZMod p) :
    lbp p b (k + k') = lbp p b k * lbp p b k' := by
  have h1 : k + k' = ((k.val + k'.val : ℕ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [h1, lbp_natCast p b hb, pow_add]
  rfl

theorem gLBConj_lbp_ne {p : ℕ} [NeZero p] (hp : p.Prime) {b : X} (hb : b ^ p = 1)
    {L : Subgroup X} (hbn : b ∉ Subgroup.normalizer (L : Set X)) {i j : ZMod p} (hij : i ≠ j) :
    GLBConj (lbp p b i) L ≠ GLBConj (lbp p b j) L := by
  intro h
  have h1 : GLBConj (lbp p b i * (lbp p b j)⁻¹) L = L := by
    have := congrArg (GLBConj (lbp p b j)⁻¹) h
    rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
    exact this
  have h2 : lbp p b i * (lbp p b j)⁻¹ = b ^ ((i.val : ℤ) - j.val) := by
    unfold lbp
    rw [zpow_sub, zpow_natCast, zpow_natCast]
  have h3 : b ^ ((i.val : ℤ) - j.val) ∈ Subgroup.normalizer (L : Set X) := by
    rw [← h2, mem_normalizer_iff_gLBConj_eq]; exact h1
  refine hbn (mem_of_zpow_mem hp hb ?_ h3)
  intro hd
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  push_cast at this
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  exact hij (sub_eq_zero.1 this)

theorem lphi_range {p : ℕ} [NeZero p] (b : X) (L : Subgroup X) (k : ZMod p) :
    (lphi p b L k).range = GLBConj (lbp p b k) L := by
  unfold lphi GLBConj
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem lPsi_range {p : ℕ} [NeZero p] {b : X} {L : Subgroup X} (hc : LComm p b L) :
    (lPsi hc).range = ⨆ k : ZMod p, GLBConj (lbp p b k) L := by
  have h := MonoidHom.noncommPiCoprod_range (fun k => lphi p b L k)
    (hcomm := fun i j h => hc i j h)
  refine h.trans ?_
  simp only [lphi_range]

attribute [local instance] i116pI_act

theorem J_eq_range [Finite X] {p : ℕ} [NeZero p] (hp : p.Prime) {B L : Subgroup X} {b : X}
    (hb : b ∈ B) (hbp : b ^ p = 1) (hbn : b ∉ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p) (hc : LComm p b L) :
    (⨆ g ∈ B, GLBConj g L : Subgroup X) = (lPsi hc).range := by
  rw [lPsi_range]
  have hcard : (MulAction.orbit ↥B L).ncard = p := by
    rw [← MulAction.index_stabilizer, i116pI_stabilizer_eq]
    exact hidx
  let f : ZMod p → Subgroup X := fun k => GLBConj (lbp p b k) L
  have finj : Function.Injective f := fun i j h => by
    by_contra hij
    exact gLBConj_lbp_ne hp hbp hbn hij h
  have hsub : Set.range f ⊆ MulAction.orbit ↥B L := by
    rintro _ ⟨k, rfl⟩
    exact (MulAction.mem_orbit_iff).2 ⟨⟨(lbp p b k)⁻¹, B.inv_mem (B.pow_mem hb _)⟩, by
      rw [i116pI_smul_sub]; simp [f]⟩
  have hrc : (Set.range f).ncard = p := by
    rw [Set.ncard_range_of_injective finj, Nat.card_zmod]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hrc]) (Set.toFinite _)
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    have hmem : GLBConj g L ∈ MulAction.orbit ↥B L :=
      (MulAction.mem_orbit_iff).2 ⟨⟨g⁻¹, B.inv_mem hg⟩, by rw [i116pI_smul_sub]; simp⟩
    rw [← heq] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact hk ▸ le_iSup f k
  · exact iSup_le fun k => le_iSup₂_of_le (lbp p b k) (B.pow_mem hb _) le_rfl

end Setup

section Main

theorem map_center_eq {X : Type*} [Group X] (L : Subgroup X) :
    (Subgroup.center ↥L).map L.subtype = L ⊓ Subgroup.centralizer (L : Set X) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_center_iff,
    Subgroup.mem_centralizer_iff, Subgroup.coe_subtype, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, hy⟩, hz, rfl⟩
    exact ⟨hy, fun g hg => congrArg Subtype.val (hz ⟨g, hg⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, fun g => Subtype.ext (hc g g.2), rfl⟩

theorem card_center_eq {X : Type*} [Group X] (L : Subgroup X) :
    Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = Nat.card ↥(Subgroup.center ↥L) := by
  rw [← map_center_eq]
  exact Subgroup.card_map_of_injective L.subtype_injective

theorem i112_layer_simple {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X} (hB : IsElemAbelian p B)
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L)
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p)
    {b : X} (hb : b ∈ B) (hbn : b ∉ Subgroup.normalizer (L : Set X))
    (hZL : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = 1 ∨
      Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = p)
    (hZ : Nat.card ↥((⨆ g ∈ B, GLBConj g L) ⊓
      Subgroup.centralizer ((⨆ g ∈ B, GLBConj g L : Subgroup X) : Set X)) < p ^ p) :
    IsSimpleGroup ↥(GLAPLayer p
      (Subgroup.centralizer ({b} : Set X) ⊓ ⨆ g ∈ B, GLBConj g L)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hbp : b ^ p = 1 := hB.2 b hb
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hcomm : LComm p b L := by
    intro i j hij x y
    have hmem : ∀ k : ZMod p, ∀ x : ↥L, lphi p b L k x ∈ GLBConj (lbp p b k) L := by
      intro k x
      rw [mem_gLBConj, lphi_apply]
      have : lbp p b k * ((lbp p b k)⁻¹ * (x : X) * lbp p b k) * (lbp p b k)⁻¹ = x := by group
      rw [this]
      exact x.2
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute
      (isComponentOf_gLBConj hLc (lbp p b i)) (isComponentOf_gLBConj hLc (lbp p b j)) with h | h
    · exact absurd h (gLBConj_lbp_ne hp hbp hbn hij)
    · exact h _ (hmem i x) _ (hmem j y)
  have hJ := J_eq_range hp hb hbp hbn hidx hcomm
  rw [hJ] at hZ ⊢
  have hZc : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = p := by
    rwa [← card_center_eq]
  have hZ0 : ∀ x ∈ Subgroup.center ↥L, lN hcomm x = 1 := by
    rcases lN_center_trivial_or hbp hcomm hZc with h | h
    · exact h
    · exfalso
      have hle : (Subgroup.pi Set.univ (fun _ : ZMod p => Subgroup.center ↥L)).map (lPsi hcomm) ≤
          (lPsi hcomm).range ⊓ Subgroup.centralizer (((lPsi hcomm).range : Subgroup X) : Set X) := by
        rintro _ ⟨f, hf, rfl⟩
        refine ⟨⟨f, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
        rintro _ ⟨g, rfl⟩
        exact (lPsi_central hcomm (fun k => hf k (Set.mem_univ k)) g).symm.eq
      have := Subgroup.card_le_of_le hle
      omega
  have hker : (lN hcomm).ker = Subgroup.center ↥L :=
    le_antisymm (fun x hx => lN_ker_le hcomm hx) (fun x hx => MonoidHom.mem_ker.2 (hZ0 x hx))
  have hsq : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  let e : ↥(lN hcomm).range ≃* (↥L ⧸ Subgroup.center ↥L) :=
    (QuotientGroup.quotientKerEquivRange (lN hcomm)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hs : IsSimpleGroup ↥(lN hcomm).range := MulEquiv.isSimpleGroup e
  have hperf : ⁅(lN hcomm).range, (lN hcomm).range⁆ = (lN hcomm).range := by
    have h1 : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
      have := hq.1
      rwa [commutator_def] at this
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
  have hdvd : p ∣ Nat.card ↥(lN hcomm).range := by
    rw [Nat.card_congr e.toEquiv, ← Subgroup.index_eq_card]
    exact dvd_index_center hp hq (i116e_dvd_card hp hO hL) hZc
  have hNC : (lN hcomm).range ≤
      Subgroup.centralizer ({b} : Set X) ⊓ (lPsi hcomm).range := by
    rintro _ ⟨l, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ⟨fun _ => l, rfl⟩⟩
    have := lN_conj hbp hcomm l
    calc lN hcomm l * b = b * (b⁻¹ * lN hcomm l * b) := by group
      _ = b * lN hcomm l := by rw [this]
  have hCN : ∀ c ∈ Subgroup.centralizer ({b} : Set X) ⊓ (lPsi hcomm).range,
      ∃ n ∈ (lN hcomm).range, ∃ y : X,
        (∀ d ∈ Subgroup.centralizer ({b} : Set X) ⊓ (lPsi hcomm).range, y * d = d * y) ∧
          c = n * y := by
    rintro c ⟨hcen, f, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hcen
    have h2 : b⁻¹ * lPsi hcomm f * b = lPsi hcomm f := by
      calc b⁻¹ * lPsi hcomm f * b = b⁻¹ * (b * lPsi hcomm f) := by rw [mul_assoc, ← h1]
        _ = lPsi hcomm f := by group
    obtain ⟨l, z, hz, hfz⟩ := lPsi_centralizer hbp hcomm h2
    refine ⟨lN hcomm l, ⟨l, rfl⟩, lPsi hcomm z, ?_, hfz⟩
    rintro d ⟨_, g, rfl⟩
    exact (lPsi_central hcomm hz g).eq
  have hlay := glaPLayer_eq_of_central_product hp hs hperf hNC hdvd hCN
  rw [hlay]
  exact hs

end Main

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
