module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbVoidCore
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAct
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open scoped commutatorElement

section Borel

variable {Y : Type*} [Group Y]

theorem isSolvable_borel [Finite Y] {L T : Subgroup Y} (hT : IsSylowTwoOf T L) :
    Group.IsSolvable ↥(L ⊓ Subgroup.normalizer (T : Set Y)) := by
  obtain ⟨hTL, h2, hodd⟩ := hT
  set N : Subgroup Y := L ⊓ Subgroup.normalizer (T : Set Y) with hN
  have hTN : T ≤ N := le_inf hTL Subgroup.le_normalizer
  have hNL : N ≤ L := inf_le_left
  have hnorm : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr inf_le_right
  have hidx : (T.subgroupOf N).index ∣ (T.subgroupOf L).index := by
    have h := Subgroup.relIndex_mul_relIndex T N L hTN hNL
    exact ⟨N.relIndex L, h.symm⟩
  have hoddq : Odd (Nat.card (↥N ⧸ T.subgroupOf N)) := by
    show Odd (T.subgroupOf N).index
    rw [Nat.odd_iff]
    by_contra hne
    have h2d : 2 ∣ (T.subgroupOf N).index := by omega
    exact hodd (h2d.trans hidx)
  have hq : Group.IsSolvable (↥N ⧸ T.subgroupOf N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddq
  have hp : IsPGroup 2 (T.subgroupOf N) := by
    intro g
    obtain ⟨k, hk⟩ := h2 (⟨g.1.1, g.2⟩ : T)
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun t : T => t.1) hk))⟩
  have : Group.IsNilpotent (T.subgroupOf N) := hp.isNilpotent
  have hK : Group.IsSolvable (T.subgroupOf N) := inferInstance
  exact Group.isSolvable_of_ker_le_range (T.subgroupOf N).subtype (QuotientGroup.mk' (T.subgroupOf N))
    (by
      intro g hg
      exact ⟨⟨g, (QuotientGroup.eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)⟩, rfl⟩)

end Borel

section Data

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

omit [Finite Y] in
private theorem exists_mul_of_mem_sup_commute' {A B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup Y :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

omit [Finite Y] in
private theorem le_normalizer_centralizer (Lb : Subgroup Y) :
    Lb ≤ Subgroup.normalizer (Subgroup.centralizer (Lb : Set Y) : Set Y) := by
  have key : ∀ g ∈ Lb, ∀ c, c ∈ Subgroup.centralizer (Lb : Set Y) → g * c * g⁻¹ ∈
      Subgroup.centralizer (Lb : Set Y) := by
    intro g hg c hc
    have : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc g hg]; group
    rwa [this]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (Lb.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem ne_borel_of_blockIb (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) :
    ∀ T : Subgroup Y, IsSylowTwoOf T Lb → Pb ≠ Lb ⊓ Subgroup.normalizer (T : Set Y) := by
  intro T hT hPT
  have hsol : Group.IsSolvable ↥Pb := by
    rw [hPT]; exact isSolvable_borel hT
  have hPL : Pb ≤ Lb := hP.parab.1
  have hDC : D ≤ Subgroup.centralizer (Lb : Set Y) :=
    le_of_perfect_of_isSolvable (hPL.trans (le_normalizer_centralizer Lb)) hsol hD.Dperf hD.Dle
  exact hD.hxC (hDC hD.hx)

theorem compParab_of_blockIb (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb)) : CompParab Lb Pb :=
  ⟨hP.comp, hT, hP.odd, hP.parab, hP.ne, ne_borel_of_blockIb hP hD⟩

theorem exists_inner_three (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) :
    ∃ u ∈ Pb, u ^ 3 = 1 ∧ u ∉ Subgroup.centralizer (Lb : Set Y) ∧ Lift.Act Lb x u ∧
      ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({u} : Set Y) →
        W = ⊥ := by
  have hPL : Pb ≤ Lb := hP.parab.1
  have hcomm : ∀ a ∈ Pb, ∀ b ∈ Subgroup.centralizer (Lb : Set Y), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a (hPL ha)
  obtain ⟨p, hp, c, hc, hxpc⟩ := exists_mul_of_mem_sup_commute' hcomm (hD.Dle hD.hx)
  have hpc : Commute p c := hcomm p hp c hc
  have hp3 : p ^ 3 * c ^ 3 = 1 := by
    rw [← hpc.mul_pow, ← hxpc]; exact hD.hx3
  have hz : p ^ 3 ∈ Subgroup.centralizer (Lb : Set Y) := by
    have : p ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hp3
    rw [this]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 3)
  have hzL : p ^ 3 ∈ Lb := Lb.pow_mem (hPL hp) 3
  have hn3 : Nat.Coprime 3 (orderOf (p ^ 3)) := by
    have hmem : (⟨p ^ 3, hzL⟩ : Lb) ∈ Subgroup.center Lb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz g.1 g.2)
    have h1 : orderOf (⟨⟨p ^ 3, hzL⟩, hmem⟩ : Subgroup.center Lb) ∣
        Nat.card (Subgroup.center Lb) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨⟨p ^ 3, hzL⟩, hmem⟩ : Subgroup.center Lb) = orderOf (p ^ 3) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact Nat.Coprime.coprime_dvd_right (h2 ▸ h1) hD.cop
  generalize hn : orderOf (p ^ 3) = n at hn3
  have hn1 : (p ^ 3) ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
  have hmod : n * n % 3 = 1 := by
    have h0 : ¬ 3 ∣ n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hn3
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hxm : x ^ (n * n) = x := by
    generalize n * n = m at hmod
    obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t + 1 := ⟨m / 3, by omega⟩
    rw [pow_succ, pow_mul, hD.hx3, one_pow, one_mul]
  have hactp : Lift.Act Lb x p := by
    intro l hl
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
    rw [hxpc]
    calc p * c * l * (p * c)⁻¹ = p * (c * l) * c⁻¹ * p⁻¹ := by group
      _ = p * (l * c) * c⁻¹ * p⁻¹ := by rw [hcl]
      _ = p * l * p⁻¹ := by group
  have hactu : Lift.Act Lb x (p ^ (n * n)) := by
    have := Lift.act_pow (hPL hp) hactp (n * n)
    rwa [hxm] at this
  have hu3 : (p ^ (n * n)) ^ 3 = 1 := by
    calc (p ^ (n * n)) ^ 3 = ((p ^ 3) ^ n) ^ n := by
          simp only [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hn1, one_pow]
  refine ⟨p ^ (n * n), Pb.pow_mem hp _, hu3, ?_, hactu, ?_⟩
  · intro hu
    apply hD.hxC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hactu l hl
    have h2 : p ^ (n * n) * l * (p ^ (n * n))⁻¹ = l := by
      rw [← (Subgroup.mem_centralizer_iff.mp hu l hl)]; group
    rw [h2] at h1
    calc l * x = (x * l * x⁻¹) * x := by rw [h1]
      _ = x * l := by group
  · intro W hW hWp hWc
    refine hD.free W hW hWp fun w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 := hactu w (hW hw)
    have h2 := Subgroup.mem_centralizer_iff.mp (hWc hw) _ (Set.mem_singleton _)
    have h3 : x * w * x⁻¹ = w := by
      rw [h1, h2]; group
    calc x * w = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [h3]

theorem blockIb_false_of_centPerfectNoncyc {𝔉 : (X : Type) → [Group X] → Prop}
    (h : KFactCentNoncycThree 𝔉) (hP : BlockIbParab Lb Pb)
    (h𝔉 : 𝔉 (↥Lb ⧸ Subgroup.center ↥Lb)) (hD : BlockIbData Lb Pb D x) : False := by
  obtain ⟨u, huP, hu3, huC, -, hfree⟩ := exists_inner_three hP hD
  obtain ⟨V, hV, hVp, Q, hQV, -, hQ⟩ :=
    h Y Lb hP.comp hP.odd h𝔉 u (hP.parab.1 huP) hu3 huC
  have hVbot : V = ⊥ := hfree V (hV.trans inf_le_left) hVp (hV.trans inf_le_right)
  have hQbot : Q = ⊥ := le_bot_iff.mp (hVbot ▸ hQV)
  subst hQbot
  exact hQ inferInstance

end Data

end CFSG.HardMathSupport.Curtis.UnitaryLevi
