module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHSplit
public import CFSG.ClassicalInvolution.Asc77.AscIHThm2
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHRed

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Four

variable {H : Type} [Group H]

theorem thm5IH_mem_zpowers_involution {z x : H} (hz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ 2 = 1 := by rw [sq]; exact hz
  have h : z ^ n = z ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul]
    simp [h2]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h, h0]
    simp
  · right
    rw [h, h1]
    simp

theorem thm5IH_mem_four {A : Subgroup H} (hA2 : ∀ a ∈ A, a * a = 1) (hA4 : Nat.card A = 4)
    {z u : H} (hz : z ∈ A) (hu : u ∈ A) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∀ a ∈ A, a = 1 ∨ a = z ∨ a = u ∨ a = z * u := by
  intro a ha
  have hzz : z * z = 1 := hA2 z hz
  have huu : u * u = 1 := hA2 u hu
  have hE : Subgroup.zpowers z ≤ A := (Subgroup.zpowers_le).mpr hz
  have hcard : 2 ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hzz) hz1]
  have huE : u ∉ Subgroup.zpowers z := by
    intro h
    rcases thm5IH_mem_zpowers_involution hzz h with h1 | h1
    · exact hu1 h1
    · exact huz h1
  rcases thm5IH_mem_or_mul_mem hE hA4 hcard hu huE ha with h | h
  · rcases thm5IH_mem_zpowers_involution hzz h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    rcases thm5IH_mem_zpowers_involution hzz h with h1 | h1
    · right; right; left
      calc a = a * u * u⁻¹ := by group
        _ = u := by rw [h1, one_mul, hui]
    · right; right; right
      calc a = a * u * u⁻¹ := by group
        _ = z * u := by rw [h1, hui]

theorem thm5IH_inducedImage_eq_closure {L A : Subgroup H} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA4 : Nat.card A = 4) {z u : H} (hz : z ∈ A) (hu : u ∈ A) (hz1 : z ≠ 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hAN : A ≤ Subgroup.normalizer (L : Set H)) :
    inducedImage L A = Subgroup.closure {toInducedAutOn L ⟨u, hAN hu⟩,
      toInducedAutOn L ⟨z, hAN hz⟩} := by
  apply le_antisymm
  · rintro _ ⟨⟨a, haN⟩, ha, rfl⟩
    have ha' : a ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hgen1 : toInducedAutOn L ⟨u, hAN hu⟩ ∈ Subgroup.closure {toInducedAutOn L ⟨u, hAN hu⟩,
        toInducedAutOn L ⟨z, hAN hz⟩} := Subgroup.subset_closure (Set.mem_insert _ _)
    have hgen2 : toInducedAutOn L ⟨z, hAN hz⟩ ∈ Subgroup.closure {toInducedAutOn L ⟨u, hAN hu⟩,
        toInducedAutOn L ⟨z, hAN hz⟩} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases thm5IH_mem_four hA2 hA4 hz hu hz1 hu1 huz a ha' with h | h | h | h
    · have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set H))) = 1 := Subtype.ext h
      rw [this, map_one]
      exact Subgroup.one_mem _
    · have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set H))) = ⟨z, hAN hz⟩ := Subtype.ext h
      rw [this]
      exact hgen2
    · have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set H))) = ⟨u, hAN hu⟩ := Subtype.ext h
      rw [this]
      exact hgen1
    · have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set H))) =
          ⟨z, hAN hz⟩ * ⟨u, hAN hu⟩ := Subtype.ext h
      rw [this, map_mul]
      exact Subgroup.mul_mem _ hgen2 hgen1
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨u, hAN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    · exact ⟨⟨z, hAN hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩

end Four

section Bridge

theorem thm5IH_injOn_of_card_le {K H : Type} [Group K] [Group H] (ψ : K →* H) {R : Subgroup K}
    [Finite R] (h : Nat.card R ≤ Nat.card (R.map ψ)) : ∀ x ∈ R, ∀ y ∈ R, ψ x = ψ y → x = y := by
  have hb := (ψ.subgroupMap_surjective R).bijective_of_nat_card_le h
  intro x hx y hy hxy
  have : ψ.subgroupMap R ⟨x, hx⟩ = ψ.subgroupMap R ⟨y, hy⟩ := Subtype.ext hxy
  exact congrArg Subtype.val (hb.1 this)

variable {p f : ℕ} [Fact p.Prime]

theorem t5Base_twin_of_twinInnerAlpha (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag}
    {k e : ℕ} (hfund : IsFundTag t) (hadm : StatedLieAdmissible t k p e) (hef : e = f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hTI : TwinInnerAlpha p e t k) {H : Type} [Group H]
    [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (eK : Nonempty (↥(R.map ψ) ≃* SL(2, GaloisField p f)))
    (eJ : Nonempty (↥(R'.map ψ) ≃* SL(2, GaloisField p f)))
    (hne : R.map ψ ≠ R'.map ψ) (hcomm : Commutes (R.map ψ) (R'.map ψ)) {z : H}
    (hz : IsUniqueInvolution (R.map ψ) z) (hzJ : z ∈ R'.map ψ) {A : Subgroup H}
    (hA : IsElemAbelian2 A 2) (hAKJ : A ≤ R.map ψ ⊔ R'.map ψ) (hzA : z ∈ A) :
    alphaOf (inducedImage ψ.range A) = ⊥ := by
  subst hef
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
  have hxR : sl2Inv eR ∈ R := sl2Inv_mem eR
  have hx2 : sl2Inv eR * sl2Inv eR = 1 := sl2Inv_mul_self hodd eR
  have hx1 : sl2Inv eR ≠ 1 := sl2Inv_ne_one hodd eR
  have hψx : ψ (sl2Inv eR) = z := by
    have hmem : ψ (sl2Inv eR) ∈ R.map ψ := Subgroup.mem_map_of_mem ψ hxR
    have hsq : ψ (sl2Inv eR) * ψ (sl2Inv eR) = 1 := by rw [← map_mul, hx2, map_one]
    rcases hz.unique _ hmem hsq with h | h
    · exact absurd (hinjR _ hxR 1 R.one_mem (by rw [h, map_one])) hx1
    · exact h
  obtain ⟨y, hyR', hyz⟩ := Subgroup.mem_map.mp hzJ
  have hy2 : y * y = 1 :=
    hinjR' (y * y) (R'.mul_mem hyR' hyR') 1 R'.one_mem (by rw [map_mul, hyz, hz.sq, map_one])
  have hy1 : y ≠ 1 := fun h => hz.ne_one (by rw [← hyz, h, map_one])
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hyx' : y = sl2Inv eR' := eq_sl2Inv_of_orderOf_eq_two hodd eR' hyR' hyord
  have hpair : TwinPairOn t (modelUniv t k p e Fact.out) ψ R R' (sl2Inv eR) (sl2Inv eR') :=
    { ker := hker
      mem := hR
      mem' := hR'
      ne := fun h => hne (by rw [h])
      comm := ih8_commutes_of_commutes_map ψ hker (hperf R hR) hcomm
      hx := hxR
      hx2 := hx2
      hx1 := hx1
      hx' := sl2Inv_mem eR'
      hx'2 := sl2Inv_mul_self hodd eR'
      hx'1 := sl2Inv_ne_one hodd eR'
      same := by rw [hψx, ← hyx', hyz] }
  obtain ⟨u, huA, hu1, huz⟩ := thm5IH_exists_ne hA4 1 z
  have hLn : A ≤ Subgroup.normalizer (ψ.range : Set H) := fun a ha =>
    Subgroup.le_normalizer
      (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R') (hAKJ ha))
  have hmain := hTI H ψ R R' (sl2Inv eR) (sl2Inv eR') hpair u (hLn huA) (hAKJ huA) (hA2 u huA)
    hu1 (by rw [hψx]; exact huz)
  have hzz : (⟨ψ (sl2Inv eR), FrameVertex.mem_normalizer_range ψ (sl2Inv eR)⟩ :
      ↥(Subgroup.normalizer (ψ.range : Set H))) = ⟨z, hLn hzA⟩ := Subtype.ext hψx
  rw [hzz] at hmain
  rw [thm5IH_inducedImage_eq_closure hA2 hA4 hzA huA hz.ne_one hu1 huz hLn]
  exact hmain

theorem t5BaseAt_twin_of_twinInnerAlpha {t : StatedLieTag} {k e : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    (hTI : p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t k p e → TwinInnerAlpha p e t k) :
    T5BaseAt p f t k e id := by
  intro hp2 hq hfund hadm hef H _ _ ψ hker R hR R' hR' eK eJ hne hcomm z hz hzJ A hA hAKJ hzA _
  have hef' : e = f := hef.resolve_right fun h => hD4 h.1
  have hq' : 5 ≤ p ^ e := by
    rw [hef']
    exact hq
  exact t5Base_twin_of_twinInnerAlpha hp2 hq hfund hadm hef' hG2 hD4 (hTI hp2 hq' hadm) ψ hker hR
    hR' eK eJ hne hcomm hz hzJ hA hAKJ hzA

theorem t5BaseAt_twin_odd {k e : ℕ} : T5BaseAt p f .POmegaOdd k e id :=
  t5BaseAt_twin_of_twinInnerAlpha (by decide) (by decide) fun hp2 hq hadm =>
    twinInnerAlpha_odd hp2 hq hadm

theorem t5BaseAt_twin_plus {k e : ℕ} (hk : 5 ≤ k) : T5BaseAt p f .POmegaPlus k e id :=
  t5BaseAt_twin_of_twinInnerAlpha (by decide) (by decide) fun hp2 hq hadm =>
    twinInnerAlpha_plus hp2 hq hadm hk

theorem t5BaseAt_twin_minus {k e : ℕ} : T5BaseAt p f .POmegaMinus k e id :=
  t5BaseAt_twin_of_twinInnerAlpha (by decide) (by decide) fun hp2 hq hadm =>
    twinInnerAlpha_minus hp2 hq hadm

end Bridge

end CFSG.ClassicalInvolution.Asc77
