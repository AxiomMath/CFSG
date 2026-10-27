module

public import CFSG.GH74.Generic.BProg.B3.S1ThreeRank2
public import CFSG.GH74.Generic.BProg.B3.S1ThreeReduce

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
open CFSG.GH74.GLS.C3.Layer1 Subgroup
open CFSG.GH74.Filter.ClassicalOdd (Q8)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem bar_sq_of_sq {a : G} {E : Subgroup G} (hE : ∀ e ∈ E, e * e = 1) :
    ∀ e ∈ PumpCalc.bar a E, e * e = 1 := by
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul]
  have : d * d = 1 := Subtype.ext (hE d hd)
  rw [this, map_one]

omit [Finite G] in
theorem rhoL_sq_of_sq {X : Type} [Group X] {L E : Subgroup X} (hE : ∀ e ∈ E, e * e = 1) :
    ∀ b ∈ (E.subgroupOf (normalizer (L : Set X))).map (rhoL L), b * b = 1 := by
  rintro _ ⟨n, hn, rfl⟩
  rw [← map_mul]
  have : n * n = 1 := Subtype.ext (hE n hn)
  rw [this, map_one]

section Alpha


theorem s1three_alpha {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G} (hc : Ctx21 G x K A a D J)
    (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) {φA φB : Q8 →* CentralizerBar a}
    (hd : S1ThreeData x a φA φB) (hB : ∀ q, φB q ∈ PumpCalc.bar a J)
    (hA : ∀ q, ∀ j ∈ PumpCalc.bar a J, φA q * j = j * φA q)
    (hperf : ∀ P : Subgroup (CentralizerBar a), ⁅P, P⁆ = P →
      P ≤ centralizer ({bar a x} : Set (CentralizerBar a)) → P = ⊥) : False := by
  classical
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc h1
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hAcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc' =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨b, hb⟩ ⟨c, hc'⟩)
  have hAsq : ∀ b ∈ A, b * b = 1 := fun b hb => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) b hb
  have hAcomm : x * a = a * x := hAcommA x hxA a hc.a_mem
  have haa : a * a = 1 := hAsq a hc.a_mem
  set Jb : Subgroup (CentralizerBar a) := PumpCalc.bar a J with hJb
  have hJc : IsComponent Jb := PumpCalc.isComponent_bar hc.obs.comp
  have hX : Gen4 (CentralizerBar a) := CFSG.GH74.Generic.S1.Exo.barC_gen4 hc.hyp.gen4
  have hcent := bar_self_central a
  have hxbar := bar_mul_bar haa hAcomm
  have hnot := xbar_not_cent hc h1
  have hψZ : ¬ ∀ m ∈ Jb, φB (QuaternionGroup.a 2) * m = m * φB (QuaternionGroup.a 2) := by
    intro h
    apply hnot
    intro j hj
    have h2 := h j hj
    rw [hd.zB] at h2
    rw [← hxbar]
    calc bar a a * bar a (x * a) * j = bar a a * (bar a (x * a) * j) := mul_assoc _ _ _
      _ = bar a a * (j * bar a (x * a)) := by rw [h2]
      _ = (bar a a * j) * bar a (x * a) := (mul_assoc _ _ _).symm
      _ = (j * bar a a) * bar a (x * a) := by rw [hcent j]
      _ = j * (bar a a * bar a (x * a)) := mul_assoc _ _ _
  have hperf' : ∀ P : Subgroup (CentralizerBar a), ⁅P, P⁆ = P → P ≤ Jb →
      P ≤ centralizer ({φB (QuaternionGroup.a 2)} : Set (CentralizerBar a)) → P = ⊥ := by
    intro P hP _ hPc
    refine hperf P hP fun p hp => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)
    rw [hd.zB] at h2
    rw [← hxbar]
    calc p * (bar a a * bar a (x * a)) = (p * bar a a) * bar a (x * a) := (mul_assoc _ _ _).symm
      _ = (bar a a * p) * bar a (x * a) := by rw [hcent p]
      _ = bar a a * (p * bar a (x * a)) := mul_assoc _ _ _
      _ = bar a a * (bar a (x * a) * p) := by rw [h2]
      _ = bar a a * bar a (x * a) * p := (mul_assoc _ _ _).symm
  have hloc : ∀ B : Subgroup (MulAut (↥Jb ⧸ center ↥Jb)), (∀ b ∈ B, b * b = 1) →
      IsLocBal32 (↥Jb ⧸ center ↥Jb) B := fun B hBsq =>
    kg3_locBal hX hJc.1 φA hd.injA hA φB hB hψZ hperf' B hBsq
  have hAN : A ≤ normalizer (J : Set G) := by
    intro e he
    have heC : e ∈ centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hAcommA e he a hc.a_mem)
    set eb : CentralizerBar a := TwoThin.barMk ↥(centralizer ({a} : Set G)) ⟨e, heC⟩ with heb
    have hy : bar a (x * a) ∈ Jb := hd.zB ▸ hB _
    have hxaC : x * a ∈ centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_centralizer_singleton_iff.2 hAcomm)
        (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    have hey : eb * bar a (x * a) * eb⁻¹ = bar a (x * a) := by
      rw [bar_of_mem hxaC]
      show proj a ⟨e, heC⟩ * proj a ⟨x * a, hxaC⟩ * (proj a ⟨e, heC⟩)⁻¹ = proj a ⟨x * a, hxaC⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show e * (x * a) * e⁻¹ = x * a
      have hex : e * (x * a) = (x * a) * e := by
        rw [← mul_assoc, hAcommA e he x hxA, mul_assoc, hAcommA e he a hc.a_mem, ← mul_assoc]
      rw [hex, mul_assoc, mul_inv_cancel, mul_one]
    set Jc : Subgroup (CentralizerBar a) := Jb.map (MulAut.conj eb).toMonoidHom with hJcdef
    have hJcc : IsComponent Jc := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj eb) hJc
    have hyc : bar a (x * a) ∈ Jc := ⟨bar a (x * a), hy, by
      show eb * bar a (x * a) * eb⁻¹ = bar a (x * a)
      exact hey⟩
    have heq : Jc = Jb := by
      by_contra hne
      have hcomm := (CFSG.LocalCores.distinct_components_commute hJcc hJc).resolve_left hne
      have hle : Jc ≤ centralizer (Jb : Set (CentralizerBar a)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      apply hψZ
      intro m hm
      rw [hd.zB]
      exact (Subgroup.mem_centralizer_iff.1 (hle hyc) m hm).symm
    exact CFSG.GH74.GLS.TwoThin.mem_normalizer_of_map_normalizes hc.obs.comp.1
      (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hc.obs.comp).2 heC heq
  obtain ⟨hDA, -, -⟩ := hc.obs.D_le
  have hDsq : ∀ d ∈ D, d * d = 1 := fun d hd => hAsq d (hDA hd)
  rcases hc.obs_cases with hD2 | ⟨hD1, hAJ⟩ | ⟨-, e', he'A, he'N, -⟩
  · exact hc.obs.not_locBal32_rank2 hD2 (hloc _ (rhoL_sq_of_sq (bar_sq_of_sq hDsq)))
  · exact hc.obs.not_locBal32_rank1 hD1 hAJ (hloc _ (rhoL_sq_of_sq (bar_sq_of_sq hAsq)))
  · exact he'N (hAN he'A)

end Alpha

end S1Three

end CFSG.GH74.Generic.BProg.B3
