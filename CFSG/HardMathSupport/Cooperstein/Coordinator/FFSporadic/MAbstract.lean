module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteB

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_of_twoA_gen {Y : Type} [Group Y]
    (hAut : ∀ φ : Y ≃* Y, ∃ s : Y, ∀ x, φ x = s * x * s⁻¹)
    (hZ : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty (L ⧸ Subgroup.center L ≃* Y) → Nat.card (Subgroup.center L) = 1)
    (hcard : Nat.card Y < 2 ^ 180) {u : Y} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hheis : ∃ (x y : Fin 4 → Y) (z : Y), HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      (∀ i, x i * u = u * x i) ∧ (∀ i, y i * u = u * y i) ∧ z * u = u * z)
    (hgen : ∃ cs : List Y, cs.length ≤ 20 ∧
      Subgroup.closure {v : Y | ∃ c ∈ cs, v = c * u * c⁻¹} = ⊤) :
    NoIrrFFOffender Y := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  by_contra hnot
  have hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hnot
  have hsup1 := card_le_card_sup_of_offender hW hq hirr hEN hE hel hoff
  have hsup2 := card_sup_le_of_outer hW hq.1 hirr hEN hel e (k := 1)
    (fun B _ _ => card_le_of_autInner hAut B)
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := hZ ↥L hq ⟨e⟩
  have hLc : Nat.card ↥L = Nat.card Y := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [this, hZ1, mul_one]
    exact Nat.card_congr e.toEquiv
  have hN : Nat.card W < 2 ^ 180 := by
    have := hsup1.trans hsup2
    rw [hLc, one_mul] at this
    exact lt_of_le_of_lt this hcard
  let π : ↥L →* Y := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπapp : ∀ b : ↥L, π b = e (QuotientGroup.mk b) := fun b => rfl
  have hker : π.ker = ⊥ := by
    have : π.ker = Subgroup.center ↥L := by
      ext x
      simp [π]
    rw [this]
    exact Subgroup.eq_bot_of_card_eq _ hZ1
  have hπi : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  obtain ⟨l0, hl0⟩ := hπs u
  have hl0sq : l0 * l0 = 1 := hπi (by rw [map_mul, hl0, hu2, map_one])
  have hl01 : l0 ≠ 1 := fun h => hu1 (by rw [← hl0, h, map_one])
  have haa : (l0 : MulAut W) * (l0 : MulAut W) = 1 := congrArg Subtype.val hl0sq
  have ha1 : (l0 : MulAut W) ≠ 1 := fun h => hl01 (Subtype.ext h)
  have hL : L ≠ ⊥ := fun hLb => ha1 ((Subgroup.eq_bot_iff_forall L).1 hLb _ l0.2)
  obtain ⟨x, y, z, h, hy3, hxc, hyc, hzc⟩ := hheis
  have hKp : ¬ 3 ∣ Nat.card π.ker := by rw [hker, Subgroup.card_bot]; norm_num
  obtain ⟨x', y', z', h', hx'1, hy'1, hz'1, -⟩ :=
    HeisCfg.exists_lift π hπs (by rw [hker]; exact bot_le) hKp h hy3
  have hcomm : ∀ g : ↥L, π g * u = u * π g → g * l0 = l0 * g := fun g hg =>
    hπi (by rw [map_mul, map_mul, hl0]; exact hg)
  have hz1 : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hH := h'.map L.subtype hz1
  have hdich := heis_dichotomy hW haa hH
    (fun i => congrArg Subtype.val (hcomm _ (by rw [hx'1]; exact hxc i)))
    (fun i => congrArg Subtype.val (hcomm _ (by rw [hy'1]; exact hyc i)))
    (congrArg Subtype.val (hcomm _ (by rw [hz'1]; exact hzc)))
  obtain ⟨cs, hcs, hcl⟩ := hgen
  have hgen' : Subgroup.closure {y : Y | ∃ c ∈ cs, ∃ b : ↥L,
      (b : MulAut W) ∈ Subgroup.zpowers (l0 : MulAut W) ∧ y = c * e (QuotientGroup.mk b) * c⁻¹} =
        ⊤ := by
    rw [eq_top_iff, ← hcl]
    refine Subgroup.closure_mono ?_
    rintro v ⟨c, hc, rfl⟩
    exact ⟨c, hc, l0, Subgroup.mem_zpowers _, (by rw [← hπapp, hl0])⟩
  have hidx := card_le_index_pow_of_closure_eq_top hq.1 hirr hL e cs hgen'
  rw [index_fixV_zpowers_eq_card_imgT] at hidx
  set t := Nat.card (imgT (l0 : MulAut W)) with ht
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW (imgT (l0 : MulAut W))
  have hfac := card_eq_card_fixV_mul_card_imgT (l0 : MulAut W)
  have hTF : t ≤ Nat.card (fixV (Subgroup.zpowers (l0 : MulAut W))) :=
    Subgroup.card_le_of_le (imgT_le_fixV_zpowers hW haa)
  rcases hdich with h1 | h1
  · have h2 : t * t ≤ Nat.card W := by
      rw [hfac, mul_comm]
      exact Nat.mul_le_mul_right _ hTF
    have h3 : 2 ^ 162 * 2 ^ 162 ≤ t * t := Nat.mul_le_mul h1 h1
    have h4 : (2 : ℕ) ^ 180 ≤ 2 ^ 162 * 2 ^ 162 := by norm_num
    exact absurd (lt_of_le_of_lt (h4.trans (h3.trans h2)) hN) (lt_irrefl _)
  · have hm8 : m ≤ 8 := by
      by_contra hm9
      have h5 : 2 ^ 18 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : 2 ^ 162 * 2 ^ 18 ≤ 2 ^ 162 * t ^ 2 := by
        rw [ht, hm, ← pow_mul, mul_comm m 2]
        exact Nat.mul_le_mul_left _ h5
      have h7 : (2 : ℕ) ^ 180 ≤ 2 ^ 162 * 2 ^ 18 := by norm_num
      exact absurd (lt_of_le_of_lt (h7.trans (h6.trans h1)) hN) (lt_irrefl _)
    have h8 : t ≤ 2 ^ 8 := by rw [ht, hm]; exact Nat.pow_le_pow_right (by norm_num) hm8
    have h9 : t ^ cs.length ≤ (2 ^ 8) ^ 20 :=
      (Nat.pow_le_pow_left h8 _).trans (Nat.pow_le_pow_right (by norm_num) hcs)
    have h10 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by rw [ht, hm]; exact Nat.two_pow_pos m)
    have h11 : 2 ^ 162 ≤ 2 ^ 162 * t ^ 2 := Nat.le_mul_of_pos_right _ h10
    have h12 : ((2 : ℕ) ^ 8) ^ 20 < 2 ^ 162 := by norm_num
    exact absurd (lt_of_le_of_lt (h11.trans (h1.trans (hidx.trans h9))) h12) (lt_irrefl _)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
