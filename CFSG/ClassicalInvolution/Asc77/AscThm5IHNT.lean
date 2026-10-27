module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHInner
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTwin
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpMain
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open scoped commutatorElement MatrixGroups

section Toral

variable {Q : Type} [Group Q] [Finite Q]

theorem thm5IH_alphaOf_eq_bot_of_toral {m : ℕ} {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {Qn : ℕ → ℕ → ℕ → Prop} (hQ : Qn n p e) (hSB : StrongLocalTwoBalanceToralPowOn m t Qn)
    [Group.IsPerfect (modelUniv t n p e hp).K] (ψ : (modelUniv t n p e hp).K →* Q)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {A : Subgroup Q}
    (hA2 : ∀ x ∈ A, x * x = 1) (hAcard : Nat.card A = 4)
    (hAN : A ≤ Subgroup.normalizer (ψ.range : Set Q))
    (hfaith : ∀ a ∈ A, a ≠ 1 → ¬ ∀ y ∈ ψ.range, a * y = y * a)
    (htoral : ∃ P : Subgroup (modelUniv t n p e hp).K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      ∀ a ∈ A, ∃ x ∈ P, x ^ m = 1 ∧ ∀ y ∈ ψ.range, a * y * a⁻¹ = ψ x * y * (ψ x)⁻¹) :
    alphaOf (inducedImage ψ.range A) = ⊥ := by
  classical
  obtain ⟨hcen, hnorm, hcent⟩ := FrameVertex.innerHom_spec ψ hker
  set L : Subgroup Q := ψ.range with hL
  have hF : inducedImage L A = ((toInducedAutOn L).comp (Subgroup.inclusion hAN)).range :=
    thm5IH_inducedImage_eq_range hAN
  have hcardF : Nat.card (inducedImage L A) = 4 := thm5IH_card_inducedImage hAN hAcard hfaith
  have hFsq : ∀ f ∈ inducedImage L A, f * f = 1 := by
    intro f hf
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hA2 b b.2)
    rw [this, map_one]
  have hFfaith : ∀ f ∈ inducedImage L A, f ≠ 1 →
      ¬ ∀ x ∈ (FrameVertex.innerHom ψ).range, f * x = x * f :=
    fun f _ hf1 hall => hf1 (hcent f hall)
  obtain ⟨P, hPc, hPact⟩ := htoral
  have htor : ToralActionPow m (FrameVertex.innerHom ψ) (inducedImage L A) := by
    refine ⟨P, hPc, fun f hf => ?_⟩
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    obtain ⟨x, hxP, hxm, hxact⟩ := hPact b b.2
    refine ⟨x, hxP, hxm, fun y => ?_⟩
    rw [FrameVertex.innerHom_apply, FrameVertex.innerHom_apply]
    show toInducedAutOn L ⟨b, hAN b.2⟩ * toInducedAutOn L ⟨ψ y, _⟩ *
      (toInducedAutOn L ⟨b, hAN b.2⟩)⁻¹ = toInducedAutOn L ⟨ψ (x * y * x⁻¹), _⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hxact (ψ y) ⟨y, rfl⟩
    show (b : Q) * ψ y * (b : Q)⁻¹ = ψ (x * y * x⁻¹)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hSC := hSB n p e hp hQ hfund hadm hp2 h5 ↥(inducedAutOn L) (FrameVertex.innerHom ψ)
    (fun g hg => hcen g (MonoidHom.mem_ker.mp hg)) hnorm (inducedImage L A) hcardF hFsq hFfaith
    htor
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd g hg
    have hc := hSC.2 a ha ha1 d hd g hg
    have hu : ((g * d)⁻¹ * (d * g)) = 1 := by
      apply hcent
      intro y hy
      have h1 := hc y hy
      calc (g * d)⁻¹ * (d * g) * y = (g * d)⁻¹ * ((d * g) * y * (d * g)⁻¹) * (d * g) := by group
        _ = (g * d)⁻¹ * ((g * d) * y * (g * d)⁻¹) * (d * g) := by
          rw [show (d * g) * y * (d * g)⁻¹ = d * g * y * (d * g)⁻¹ from rfl, h1]
        _ = y * ((g * d)⁻¹ * (d * g)) := by group
    have hdg : d * g = g * d := by
      have := congrArg (fun w => (g * d) * w) hu
      simpa [mul_assoc] using this
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc d * g * d⁻¹ * g⁻¹ = (g * d) * d⁻¹ * g⁻¹ := by rw [hdg]
      _ = 1 := by group
  · rw [eq_bot_iff]
    intro d hd
    have hd' : d ∈ deltaCore (inducedImage L A) := hd
    rw [Subgroup.mem_bot]
    exact hcent d fun y hy => hSC.1 d hd' y hy

end Toral

section Structure

variable {H : Type} [Group H] [Finite H]

theorem thm5IH_mem_four_nt {K J : Subgroup H} {z t : H} (hKJ : Commutes K J)
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzJ : z ∉ J) {u : H}
    (hu : u ∈ K ⊔ J) (hu2 : u * u = 1) : u = 1 ∨ u = z ∨ u = t ∨ u = z * t := by
  obtain ⟨k, hk, j, hj, hkj⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hKJ hu
  have hkjc : k * j = j * k := hKJ k hk j hj
  have hkk : k * k = (j * j)⁻¹ := by
    have h : (k * k) * (j * j) = 1 := by
      calc (k * k) * (j * j) = k * (k * j) * j := by group
        _ = k * (j * k) * j := by rw [hkjc]
        _ = (k * j) * (k * j) := by group
        _ = u * u := by rw [hkj]
        _ = 1 := hu2
    exact eq_inv_of_mul_eq_one_left h
  obtain ⟨c, hc⟩ : ∃ c : H, c = k * k := ⟨_, rfl⟩
  have hcK : c ∈ K := by
    rw [hc]
    exact K.mul_mem hk hk
  have hcj : c = (j * j)⁻¹ := hc.trans hkk
  have hcJ : c ∈ J := by
    rw [hcj]
    exact J.inv_mem (J.mul_mem hj hj)
  have hodd : Odd (orderOf c) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have hpos : 0 < orderOf c := orderOf_pos c
    have hm0 : m ≠ 0 := by omega
    have hdvd : m ∣ orderOf c := ⟨2, by omega⟩
    have hord : orderOf (c ^ m) = 2 := by
      rw [orderOf_pow_of_dvd hm0 hdvd, hm, ← two_mul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hw2 : c ^ m * c ^ m = 1 := by
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    have hw1 : c ^ m ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    rcases hz.unique _ (K.pow_mem hcK m) hw2 with h | h
    · exact hw1 h
    · exact hzJ (h ▸ J.pow_mem hcJ m)
  set d := orderOf c with hd
  have hcd : c ^ d = 1 := pow_orderOf_eq_one c
  have hkd2 : k ^ d * k ^ d = 1 := by
    calc k ^ d * k ^ d = (k * k) ^ d := by rw [← pow_add, ← two_mul, pow_mul, pow_two]
      _ = 1 := by rw [← hc]; exact hcd
  have hjd2 : j ^ d * j ^ d = 1 := by
    calc j ^ d * j ^ d = (j * j) ^ d := by rw [← pow_add, ← two_mul, pow_mul, pow_two]
      _ = (((j * j)⁻¹) ^ d)⁻¹ := by rw [inv_pow, inv_inv]
      _ = (c ^ d)⁻¹ := by rw [hcj]
      _ = 1 := by rw [hcd, inv_one]
  have hud : u ^ d = u := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, pow_two, hu2, one_pow, one_mul]
  have hukj : u ^ d = k ^ d * j ^ d := by
    rw [← hkj]
    exact (Commute.mul_pow (show Commute k j from hkjc) d)
  have hu' : u = k ^ d * j ^ d := hud.symm.trans hukj
  rcases hz.unique _ (K.pow_mem hk d) hkd2 with h1 | h1 <;>
    rcases ht.unique _ (J.pow_mem hj d) hjd2 with h2 | h2
  · left
    rw [hu', h1, h2, one_mul]
  · right; right; left
    rw [hu', h1, h2, one_mul]
  · right; left
    rw [hu', h1, h2, mul_one]
  · right; right; right
    rw [hu', h1, h2]

end Structure


section Main

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_nt_of_strong {t : StatedLieTag} {k e : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {Qn : ℕ → ℕ → ℕ → Prop} (hQ : Qn k p e)
    (hSB : StrongLocalTwoBalanceToralPowOn 2 t Qn) : T5BaseAt p f t k e Not := by
  intro hp2 hq hfund hadm hef H _ _ ψ hker R hR R' hR' eK eJ hne hcomm z hz hzJ A hA hAKJ hzA
    hfaith
  have hef' : e = f := hef.resolve_right fun h => hD4 h.1
  subst hef'
  obtain ⟨eK⟩ := eK
  obtain ⟨eJ⟩ := eJ
  have hA4 : Nat.card A = 4 := by simpa using hA.1
  have hA2 : ∀ a ∈ A, a * a = 1 := hA.2
  have hf0 : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e hf0]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hperf := CFSG.ClassicalInvolution.RouteD.Gaps.fundPerfect_modelUniv hp2 hfund hadm (by omega)
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2
    (isFundTag_modelFacts hfund) hadm hG2 hD4 hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2
    (isFundTag_modelFacts hfund) hadm hG2 hD4 hR'
  have hFinR : Finite ↥R := Finite.of_equiv _ eR.symm.toEquiv
  have hFinR' : Finite ↥R' := Finite.of_equiv _ eR'.symm.toEquiv
  have hinjR : ∀ x ∈ R, ∀ y ∈ R, ψ x = ψ y → x = y := by
    refine thm5IH_injOn_of_card_le ψ ?_
    rw [Nat.card_congr eR.toEquiv, Nat.card_congr eK.toEquiv]
  have hinjR' : ∀ x ∈ R', ∀ y ∈ R', ψ x = ψ y → x = y := by
    refine thm5IH_injOn_of_card_le ψ ?_
    rw [Nat.card_congr eR'.toEquiv, Nat.card_congr eJ.toEquiv]
  have hcommRR' : Commutes R R' := ih8_commutes_of_commutes_map ψ hker (hperf R hR) hcomm
  have hxR : sl2Inv eR ∈ R := sl2Inv_mem eR
  have hx2 : sl2Inv eR * sl2Inv eR = 1 := sl2Inv_mul_self hodd eR
  have hx1 : sl2Inv eR ≠ 1 := sl2Inv_ne_one hodd eR
  have hψx : ψ (sl2Inv eR) = z := by
    have hmem : ψ (sl2Inv eR) ∈ R.map ψ := Subgroup.mem_map_of_mem ψ hxR
    have hsq : ψ (sl2Inv eR) * ψ (sl2Inv eR) = 1 := by rw [← map_mul, hx2, map_one]
    rcases hz.unique _ hmem hsq with h | h
    · exact absurd (hinjR _ hxR 1 R.one_mem (by rw [h, map_one])) hx1
    · exact h
  have hxR' : sl2Inv eR' ∈ R' := sl2Inv_mem eR'
  have hx'2 : sl2Inv eR' * sl2Inv eR' = 1 := sl2Inv_mul_self hodd eR'
  have hx'1 : sl2Inv eR' ≠ 1 := sl2Inv_ne_one hodd eR'
  have hJt : IsUniqueInvolution (R'.map ψ) (ψ (sl2Inv eR')) :=
    { mem := Subgroup.mem_map_of_mem ψ hxR'
      ne_one := fun h => hx'1 (hinjR' _ hxR' 1 R'.one_mem (by rw [h, map_one]))
      sq := by rw [← map_mul, hx'2, map_one]
      unique := by
        rintro _ ⟨r, hr, rfl⟩ hsq
        have hr2 : r * r = 1 := hinjR' _ (R'.mul_mem hr hr) 1 R'.one_mem
          (by rw [map_mul, hsq, map_one])
        by_cases hr1 : r = 1
        · left
          rw [hr1, map_one]
        · right
          have hord : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
          rw [eq_sl2Inv_of_orderOf_eq_two hodd eR' hr hord] }
  have hAe : ∀ a ∈ A, a = 1 ∨ a = z ∨ a = ψ (sl2Inv eR') ∨ a = z * ψ (sl2Inv eR') :=
    fun a ha => thm5IH_mem_four_nt hcomm hz hJt hzJ (hAKJ ha) (hA2 a ha)
  have hLn : A ≤ Subgroup.normalizer (ψ.range : Set H) := fun a ha =>
    Subgroup.le_normalizer
      (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R') (hAKJ ha))
  have hxx' : sl2Inv eR * sl2Inv eR' = sl2Inv eR' * sl2Inv eR :=
    hcommRR' _ hxR _ hxR'
  have hcommP : ∀ a ∈ Subgroup.closure ({sl2Inv eR, sl2Inv eR'} : Set _),
      ∀ b ∈ Subgroup.closure ({sl2Inv eR, sl2Inv eR'} : Set _), a * b = b * a := by
    intro a ha b hb
    have hc : ({sl2Inv eR, sl2Inv eR'} : Set _).Pairwise Commute := by
      rintro x (rfl | rfl) y (rfl | rfl) hne
      · exact absurd rfl hne
      · exact hxx'
      · exact hxx'.symm
      · exact absurd rfl hne
    have := Subgroup.isMulCommutative_closure hc
    exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : Subgroup.closure _) ⟨b, hb⟩)
  have hperfK : Group.IsPerfect (modelUniv t k p e Fact.out).K :=
    ⟨(ModelFacts.isQuasisimple_modelUniv t k p e Fact.out hfund hadm).1⟩
  refine thm5IH_alphaOf_eq_bot_of_toral Fact.out hfund hadm hp2 hq hQ hSB ψ hker hA2 hA4 hLn
    hfaith ⟨Subgroup.closure {sl2Inv eR, sl2Inv eR'}, hcommP, fun a ha => ?_⟩
  have hxP : sl2Inv eR ∈ Subgroup.closure ({sl2Inv eR, sl2Inv eR'} : Set _) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hx'P : sl2Inv eR' ∈ Subgroup.closure ({sl2Inv eR, sl2Inv eR'} : Set _) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hsq' : (sl2Inv eR * sl2Inv eR') ^ 2 = 1 := by
    calc (sl2Inv eR * sl2Inv eR') ^ 2 = (sl2Inv eR * sl2Inv eR') * (sl2Inv eR * sl2Inv eR') := by
          rw [pow_two]
      _ = (sl2Inv eR * sl2Inv eR) * (sl2Inv eR' * sl2Inv eR') := by
          calc (sl2Inv eR * sl2Inv eR') * (sl2Inv eR * sl2Inv eR')
              = sl2Inv eR * (sl2Inv eR' * sl2Inv eR) * sl2Inv eR' := by group
            _ = sl2Inv eR * (sl2Inv eR * sl2Inv eR') * sl2Inv eR' := by rw [hxx']
            _ = (sl2Inv eR * sl2Inv eR) * (sl2Inv eR' * sl2Inv eR') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  rcases hAe a ha with h | h | h | h
  · exact ⟨1, Subgroup.one_mem _, one_pow _, fun y _ => by rw [h]; simp⟩
  · exact ⟨sl2Inv eR, hxP, by rw [pow_two]; exact hx2, fun y _ => by rw [h, hψx]⟩
  · exact ⟨sl2Inv eR', hx'P, by rw [pow_two]; exact hx'2, fun y _ => by rw [h]⟩
  · refine ⟨sl2Inv eR * sl2Inv eR', Subgroup.mul_mem _ hxP hx'P, hsq', fun y _ => ?_⟩
    rw [h, map_mul, hψx]

end Main


section Instances

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_nt_psl {k e : ℕ} : T5BaseAt p f .PSL k e Not :=
  t5BaseAt_nt_of_strong (Qn := fun _ _ _ => True) (by decide) (by decide) trivial
    StrongBalance.Linear.strongLocalTwoBalanceToralPowOn_PSL_two

theorem t5BaseAt_nt_psu {k e : ℕ} : T5BaseAt p f .PSU k e Not :=
  t5BaseAt_nt_of_strong (Qn := fun _ _ _ => True) (by decide) (by decide) trivial
    StrongBalance.Unitary.strongLocalTwoBalanceToralPowOn_PSU_two

theorem t5BaseAt_nt_psp_two {e : ℕ} : T5BaseAt p f .PSp 2 e Not :=
  t5BaseAt_nt_of_strong (Qn := fun n _ _ => n = 2) (by decide) (by decide) rfl
    (StrongLocalTwoBalanceToralPowOn.mono_order (show 2 ∣ 4 by norm_num)
      (strongLocalTwoBalanceToralPowOn_four_iff.mpr
        StrongBalance.Sp.strongLocalTwoBalanceToralFourOn_PSp_two))

end Instances


end CFSG.ClassicalInvolution.Asc77
