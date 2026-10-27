module

public import CFSG.GH74.Generic.BProg.B3.S3Boot293
public import CFSG.GH74.Generic.BProg.B3.S3Sec29wDefs
public import CFSG.GH74.Generic.BProg.B3.S3Sec29BNTrans
public import CFSG.GH74.Generic.BProg.B3.S3BootObs52

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.Stage1.Thm2
open scoped commutatorElement

namespace S3Boot293w

theorem hasSL2Model_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {P : ℕ → Prop}
    (h : HasSL2Model X P) : HasSL2Model Y P := by
  obtain ⟨F, hF, hfin, hP, ⟨e'⟩⟩ := h
  exact ⟨F, hF, hfin, hP, ⟨e.symm.trans e'⟩⟩

theorem isL2OddW_map_conj {G : Type} [Group G] (g : G) {J : Subgroup G} (h : IsL2OddW J) :
    IsL2OddW (J.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨r, m, hr, hr2, hm, hmod⟩ := h
  obtain ⟨f⟩ := S3Boot293.nonempty_quot_map_conj g J
  refine ⟨r, m, hr, hr2, hm, ?_⟩
  rcases hmod with hL | hS
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv f.symm hL)
  · exact Or.inr (hasSL2Model_of_mulEquiv f.symm hS)

theorem type_map_conj {G : Type} [Group G] (g : G) {J : Subgroup G}
    (h : IsA7Bar J ∨ IsL2OddW J) :
    IsA7Bar (J.map (MulAut.conj g).toMonoidHom) ∨ IsL2OddW (J.map (MulAut.conj g).toMonoidHom) := by
  rcases h with hA | hL
  · obtain ⟨e₂⟩ := hA
    obtain ⟨e₁⟩ := S3Boot293.nonempty_quot_map_conj g J
    exact Or.inl ⟨e₁.trans e₂⟩
  · exact Or.inr (isL2OddW_map_conj g hL)

end S3Boot293w

theorem lemma293w {G : Type} [Group G] [Finite G] (hKG : Sec29KGw G) {x a : G}
    {K A D J B : Subgroup G} (hc : Ctx21 G x K A a D J)
    (hSD : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)) (hext : IsExtSource2 x K A B) (hB4 : pRank 2 ↥B = 4)
    (hnot : ¬ (A7InGamma K A B ∧ IsKBal 3 B ∧ IsWeakKBal 2 B)) {y : G} (hyE : y ∈ A ⊓ K)
    (hy : orderOf y = 2) :
    ∃ b ∈ B, ∃ D' J' : Subgroup G, (IsA7Bar J' ∨ IsL2OddW J') ∧
      (Obs52 B b D' J' ∨ (b = y ∧ Obs32 A y D' J' ∧ D' ≤ A ∧ IsA7Bar J' ∧
        ¬ J' ≤ gammaK 2 B 3)) := by
  have h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := hSD.qShape3
  have hAB : A ≤ B := hext.1
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hext.2.2.2.1
  by_cases hA7 : A7InGamma K A B
  ·
    have hnb : ¬ (IsKBal 3 B ∧ IsWeakKBal 2 B) := fun h => hnot ⟨hA7, h⟩
    have hBE : IsE 4 ⊤ B := ⟨le_top, hBel, hext.2.2.2.2.1⟩
    obtain ⟨b, hbB, D', J', hobs⟩ := exists_obs52 hBE hnb
    exact ⟨b, hbB, D', J',
      hKG.tab52 x K A B b D' J' hc.hyp hc.noAlt hc.circ hSD hc.src hext hB4 hobs, Or.inl hobs⟩
  ·
    have hA7' := hA7
    unfold A7InGamma at hA7'
    push Not at hA7'
    obtain ⟨a₀, ha₀, ha₀1, D₀, J₀, hobs, hA7J, hnle⟩ := hA7'
    obtain ⟨E, hEK, hAE, hEel, hE4, hAKE⟩ :=
      S3Boot293.exists_E_inf_le hc.circ.1.1.1.2.2 hc.src h3
    have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
    obtain ⟨g, hg, hga⟩ := ntrans_proved G x K A B E y a₀ hc.circ.1.2.2 h3 hc.src hext hB4 hEK hAE
      hEel hE4 (hAKE hyE) hy1 (hAKE ha₀) ha₀1
    have hgA : g ∈ normalizer (A : Set G) := hg.1.2
    have hgB : g ∈ normalizer (B : Set G) := hg.2
    have hyA : y ∈ A := (Subgroup.mem_inf.1 hyE).1
    have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u :=
      (C3.Layer1.Back.forall_of_isElementaryAbelian hc.src.2.1).1
    have hobs' := S3Boot293.obs32_map_conj hobs hgA hga hy hyA hAc
    have hA7J' : IsA7Bar (J₀.map (MulAut.conj g).toMonoidHom) := by
      obtain ⟨e₁⟩ := S3Boot293.nonempty_quot_map_conj g J₀
      obtain ⟨e₂⟩ := hA7J
      exact ⟨e₁.trans e₂⟩
    have hΓ : (gammaK 2 B 3).map (MulAut.conj g⁻¹).toMonoidHom ≤ gammaK 2 B 3 := by
      have h := S3Boot293.map_gammaK_le g⁻¹ B 3
      have e : B.map (MulAut.conj g⁻¹).toMonoidHom = B :=
        Th2.cj_eq_of_mem_normalizer (Subgroup.inv_mem _ hgB)
      rwa [e] at h
    have hnle' : ¬ J₀.map (MulAut.conj g).toMonoidHom ≤ gammaK 2 B 3 := by
      intro hle
      apply hnle
      intro j hj
      have hj' : g * j * g⁻¹ ∈ gammaK 2 B 3 := hle ⟨j, hj, rfl⟩
      have : g⁻¹ * (g * j * g⁻¹) * g⁻¹⁻¹ ∈ (gammaK 2 B 3).map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨g * j * g⁻¹, hj', by simp⟩
      rw [show g⁻¹ * (g * j * g⁻¹) * g⁻¹⁻¹ = j by group] at this
      exact hΓ this
    exact ⟨y, hAB hyA, D₀.map (MulAut.conj g).toMonoidHom, J₀.map (MulAut.conj g).toMonoidHom,
      Or.inl hA7J', Or.inr ⟨rfl, hobs', hobs'.D_le.1, hA7J', hnle'⟩⟩

end CFSG.GH74.Generic.BProg.B3
