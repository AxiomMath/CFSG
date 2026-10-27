module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorLie
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternToral
public import CFSG.ClassicalInvolution.RouteD.GapsFrIso
public import CFSG.ClassicalInvolution.RouteD.GapsFrModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem spin6_chain_frame (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R0 R1 R2 RN RM : Subgroup (spinGroup (quadPlus 6 (GaloisField p f)))}
    (h0 : R0 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (h1 : R1 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (h2 : R2 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hN : RN ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hM : RM ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hadj01 : ModelAdj (Subgroup.center _) R0 R1) (hadj12 : ModelAdj (Subgroup.center _) R1 R2)
    (hlin01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W R0 R1)
    (hlin12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W R1 R2)
    (hc02 : Commutes R0 R2) (hM0 : Commutes RM R0) (hM1 : Commutes RM R1)
    (hM2 : Commutes RM R2) (hadjN : ModelAdj (Subgroup.center _) R0 RN)
    (hcN : Commutes R2 RN) :
    ∃ x : spinGroup (quadPlus 6 (GaloisField p f)),
      R0 = (rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 0 1 (by norm_num) (by norm_num)
        (by norm_num) true false).map (MulAut.conj x).toMonoidHom ∧
      R1 = (rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 1 2 (by norm_num) (by norm_num)
        (by norm_num) true false).map (MulAut.conj x).toMonoidHom ∧
      R2 = (rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 2 3 (by norm_num) (by norm_num)
        (by norm_num) true false).map (MulAut.conj x).toMonoidHom ∧
      ∃ t : Bool, RM = (rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 4 5 (by norm_num)
        (by norm_num) (by norm_num) true t).map (MulAut.conj x).toMonoidHom := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin 6 ⊕ Fin 6 → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have cq := centralQuot_plus hp2 (by omega : 4 ≤ 6) hm3 hq
  obtain ⟨i2, hi2⟩ := cq.map_mem _ h2
  obtain ⟨L', hL', hLne, -, -⟩ := IsFundamental.exists_twin hodd hi2
  obtain ⟨Rtw, hRtwf, hRtw⟩ := cq.surj L' ⟨i2, hL'⟩
  have hne : Rtw ≠ R2 := by
    intro h
    exact hLne (by rw [← hRtw, h])
  have htwin : ∀ i j, IsFundamental (quadPlus 6 (GaloisField p f))
      (R2.map (spinAction (quadPlus 6 (GaloisField p f)))) i →
      IsFundamental (quadPlus 6 (GaloisField p f))
        (Rtw.map (spinAction (quadPlus 6 (GaloisField p f)))) j → i = j := by
    intro i j hi hj
    rw [hRtw] at hj
    exact (IsFundamental.involution_unique hodd hi hi2).trans
      (IsFundamental.involution_unique hodd hj hL').symm
  obtain ⟨iN, hiN⟩ := cq.map_mem _ hN
  have hdist : ∀ i j, IsFundamental (quadPlus 6 (GaloisField p f))
      (R0.map (spinAction (quadPlus 6 (GaloisField p f)))) i →
      IsFundamental (quadPlus 6 (GaloisField p f))
        (R2.map (spinAction (quadPlus 6 (GaloisField p f)))) j → i ≠ j := by
    intro i j hi hj
    have hadjV : ModelAdj (scalars (GaloisField p f) (Fin 6 ⊕ Fin 6 → GaloisField p f))
        (R0.map (spinAction (quadPlus 6 (GaloisField p f))))
        (RN.map (spinAction (quadPlus 6 (GaloisField p f)))) := cq.modelAdj h0 hN hadjN
    have hcV : Commutes (R2.map (spinAction (quadPlus 6 (GaloisField p f))))
        (RN.map (spinAction (quadPlus 6 (GaloisField p f)))) :=
      (cq.commutes_iff h2).mpr hcN
    have hc02V : Commutes (R0.map (spinAction (quadPlus 6 (GaloisField p f))))
        (R2.map (spinAction (quadPlus 6 (GaloisField p f)))) :=
      (cq.commutes_iff h0).mpr hc02
    refine (ne_of_distinguish hodd hdim hj hi hiN ?_ ?_ ?_ ?_ ?_)
    · intro e
      rw [← e] at hc02V
      exact hadjV.2.1 hc02V
    · exact fun e => hadjV.1 e.symm
    · exact modelInvComm_of_commutes hodd hiN hj (commutes_symm hcV)
    · exact (ModelInvComm.of_adj hadjV).symm'
    · intro hiff
      exact hadjV.2.1 (commutes_symm (hiff.mp (commutes_symm hcV)))
  let R : ℕ → Subgroup (spinGroup (quadPlus (2 + 4) (GaloisField p f))) := fun a =>
    if a = 0 then R0 else if a = 1 then R1 else R2
  have hR0 : R 0 = R0 := by simp [R]
  have hR1 : R 1 = R1 := by simp [R]
  have hR2 : R 2 = R2 := by simp [R]
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition hp2 hq (s := 2) (by norm_num)
    (R := R) (Rtw := Rtw) (RM := RM)
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ h0, hR1 ▸ h1, hR2 ▸ h2])
    hRtwf hM
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ hR1 ▸ hadj01, hR1 ▸ hR2 ▸ hadj12])
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ hR1 ▸ hlin01, hR1 ▸ hR2 ▸ hlin12])
    (fun a b hab hb => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hR0 ▸ hR2 ▸ hc02)
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ hM0, hR1 ▸ hM1, hR2 ▸ hM2])
    (fun a b hab hb => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hR0 ▸ hR2 ▸ hdist)
    hne htwin
  exact ⟨x, hR0 ▸ hxR 0 (by norm_num), hR1 ▸ hxR 1 (by norm_num), hR2 ▸ hxR 2 (by norm_num), t,
    hxM⟩

end CFSG.ClassicalInvolution.RouteD.Gaps

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.ClassicalGroups.Orthogonal

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

omit [Finite G] in
theorem torusFixedP_of_chain_model (c : ETCtx p f .POmegaPlus 6 Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z) (a₀ : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank)
    {R0 R1 R2 RN : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K}
    (h0 : R0 ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
    (h1 : R1 ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
    (h2 : R2 ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
    (hN : RN ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
    (hM : rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a₀ ∈
      fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
    (hadj01 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) R0 R1)
    (hadj12 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) R1 R2)
    (hlin01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W R0 R1)
    (hlin12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W R1 R2)
    (hc02 : Commutes R0 R2)
    (hM0 : Commutes (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a₀) R0)
    (hM1 : Commutes (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a₀) R1)
    (hM2 : Commutes (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a₀) R2)
    (hadjN : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) R0 RN)
    (hcN : Commutes R2 RN)
    (hfix0 : ∀ y ∈ R0, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y)
    (hfix1 : ∀ y ∈ R1, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y)
    (hfix2 : ∀ y ∈ R2, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y) :
    TorusFixedP (by norm_num : 3 ≤ 6) c a₀ ht := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  obtain ⟨e, ι, hcι⟩ := Gaps.exists_isoCompatPlus (p := p) (f := f) hm3
  obtain ⟨W01, hW01⟩ := hlin01
  obtain ⟨W12, hW12⟩ := hlin12
  obtain ⟨x, hx0, hx1, hx2, tt, hxM⟩ := Gaps.spin6_chain_frame c.hp2 c.hq
    (Gaps.map_symm_mem_fund_iso hm3 hcι h0) (Gaps.map_symm_mem_fund_iso hm3 hcι h1)
    (Gaps.map_symm_mem_fund_iso hm3 hcι h2) (Gaps.map_symm_mem_fund_iso hm3 hcι hN)
    (Gaps.map_symm_mem_fund_iso hm3 hcι hM)
    (Gaps.ModelAdj.map_equiv ι.symm hadj01) (Gaps.ModelAdj.map_equiv ι.symm hadj12)
    ⟨_, Gaps.linearBlockStandardPair_map_equiv ι.symm hW01⟩
    ⟨_, Gaps.linearBlockStandardPair_map_equiv ι.symm hW12⟩
    ((Gaps.commutes_map_equiv ι.symm).mpr hc02) ((Gaps.commutes_map_equiv ι.symm).mpr hM0)
    ((Gaps.commutes_map_equiv ι.symm).mpr hM1) ((Gaps.commutes_map_equiv ι.symm).mpr hM2)
    (Gaps.ModelAdj.map_equiv ι.symm hadjN) ((Gaps.commutes_map_equiv ι.symm).mpr hcN)
  let F₀ := plusFrame 6 (GaloisField p f) hm3
  let θ : spinGroup (quadPlus 6 (GaloisField p f)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  let σ := Gaps.locAut c.hΩ.conjInvariant ht
  let T : Subgroup (spinGroup (quadPlus 6 (GaloisField p f))) :=
    MonoidHom.eqLocus (σ.toMonoidHom.comp (θ.comp (MulAut.conj x).toMonoidHom))
      (θ.comp (MulAut.conj x).toMonoidHom)
  have hmemT : ∀ y, y ∈ T ↔ σ (θ (x * y * x⁻¹)) = θ (x * y * x⁻¹) := fun y => Iff.rfl
  have hle : ∀ (R : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K)
      (S : Subgroup (spinGroup (quadPlus 6 (GaloisField p f)))),
      R.map ι.symm.toMonoidHom = S.map (MulAut.conj x).toMonoidHom →
      (∀ r ∈ R, σ (c.d.ψ r) = c.d.ψ r) → S ≤ T := by
    intro R S hS hR y hy
    rw [hmemT]
    have hyR : x * y * x⁻¹ ∈ R.map ι.symm.toMonoidHom := by
      rw [hS]
      exact ⟨y, hy, rfl⟩
    obtain ⟨r, hr, hre⟩ := hyR
    have hι : ι (x * y * x⁻¹) = r := by
      rw [← hre]
      simp
    show σ (c.d.ψ (ι (x * y * x⁻¹))) = c.d.ψ (ι (x * y * x⁻¹))
    rw [hι]
    exact hR r hr
  have hA : ∀ a, a < 3 → Gaps.RootInN F₀ T a (a + 1) true false ∧
      Gaps.RootInN F₀ T (a + 1) a true false := by
    intro a ha
    interval_cases a
    · exact Gaps.rootInN_pair_of_longSL2_le (by norm_num) (by norm_num) (hle R0 _ hx0 hfix0)
    · exact Gaps.rootInN_pair_of_longSL2_le (by norm_num) (by norm_num) (hle R1 _ hx1 hfix1)
    · exact Gaps.rootInN_pair_of_longSL2_le (by norm_num) (by norm_num) (hle R2 _ hx2 hfix2)
  have hAll := Gaps.rootInN_of_A_chain (n := 3) hA
  obtain ⟨γ₀, -, hγ₀⟩ := exists_mem_rootsD_toStdD_eq 6 (i := ⟨4, by norm_num⟩)
    (j := ⟨5, by norm_num⟩) (s := boolSign true) (t := boolSign tt) (by decide)
    (boolSign_eq_one_or_eq_neg_one _) (boolSign_eq_one_or_eq_neg_one _)
  refine ⟨e, ι, hcι, ⟨4, by norm_num⟩, ⟨5, by norm_num⟩, by decide, γ₀, true, tt, hγ₀, x, T, ?_,
    ?_, fun y hy => hy⟩
  · have e1 : (plusDatum 6 (GaloisField p f) hm3).rootGroup γ₀ ⊔
        (plusDatum 6 (GaloisField p f) hm3).rootGroup (-γ₀) =
        Gaps.rootSL2 F₀ 4 5 (by norm_num) (by norm_num) (by norm_num) true tt :=
      Gaps.rootGroup_sup_eq_longSL2_range hm3 (i := ⟨4, by norm_num⟩) (j := ⟨5, by norm_num⟩)
        (by decide) true tt hγ₀
    rw [e1, ← hxM, Subgroup.map_map]
    have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
      ext y
      simp
    rw [hid, Subgroup.map_id]
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hij hi4 hi5 hj4 hj5 u
    have ha4 : a ≠ 4 := fun h => hi4 (Fin.ext h)
    have ha5 : a ≠ 5 := fun h => hi5 (Fin.ext h)
    have hb4 : b ≠ 4 := fun h => hj4 (Fin.ext h)
    have hb5 : b ≠ 5 := fun h => hj5 (Fin.ext h)
    have hab : a ≠ b := fun h => hij (Fin.ext h)
    obtain ⟨ha', hb', hab', hle'⟩ := Gaps.rootSL2_le_of_rootInN
      (hAll a b (by omega) (by omega) hab) (hAll b a (by omega) (by omega) hab.symm)
    exact hle' ⟨diagSL2 u, rfl⟩

end CFSG.ClassicalInvolution.RouteD
