module

public import CFSG.Quasithin.H13.U3S1348E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1342

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_false_of_normal_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    (hL : IsShort2 L) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    {H : Subgroup G} (hHL1 : H ≤ normalizer (L₁Of L (fsuV1 T V) : Set G))
    (hL1H : L₁Of L (fsuV1 T V) ≤ H) (hVO : V ≤ pCoreOf 2 H) (hOR : pCoreOf 2 H ≤ r1Of T L V)
    {h : G} (hh : h ∈ H) (hnot : ¬ V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hON : pCoreOf 2 H ≤ normalizer (V : Set G) :=
    hOR.trans ((r1Of_le_T T L V).trans S.frame.T_le)
  set Vh := V.map (MulAut.conj h).toMonoidHom with hVh
  have hWC := s134_V3conj_le_centralizer S he hHL1 hL1H hVO hON hh
  have hWeq := s134_V3conj_eq S hL he hHL1 hL1H hVO hh hWC
  have hV3Vh : s134V3 S ≤ Vh := hWeq ▸ map_mono (s134V3_le_V S)
  have hVhO : Vh ≤ pCoreOf 2 H := map_conj_le_of_mem_normalizer hVO (le_normalizer_pCoreOf 2 H hh)

  have hVN : ∀ v ∈ V, ∀ b ∈ Vh, v * b * v⁻¹ ∈ Vh := by
    intro v hv b hb
    have hv' : h⁻¹ * v * h ∈ pCoreOf 2 H := by
      have := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (inv_mem hh)) v).mp (hVO hv)
      simpa using this
    have h1 := (mem_normalizer_iff.mp (hON hv') _).mp (mem_map_conj_iff.1 hb)
    refine mem_map_conj_iff.2 ?_
    have e : h⁻¹ * (v * b * v⁻¹) * h =
        (h⁻¹ * v * h) * (h⁻¹ * b * h) * (h⁻¹ * v * h)⁻¹ := by group
    rw [e]
    exact h1

  obtain ⟨a, haVh, haC⟩ := Set.not_subset.1 hnot
  have haN : a ∈ normalizer (V : Set G) := hON (hVhO haVh)
  obtain ⟨v, hv, hva⟩ : ∃ v ∈ V, v * a ≠ a * v := by
    by_contra hall
    push Not at hall
    exact haC (mem_centralizer_iff.2 fun v hv => hall v hv)

  have haK : S.frame.ρ ⟨a, haN⟩ ∈ K4xList :=
    ((s134_mem_r1Of_iff S).1 (hOR (hVhO haVh))).2 haN
  have hfixW : ∀ y ∈ W3list, G6.permAct 6 (S.frame.ρ ⟨a, haN⟩) y = y := by
    intro y hy
    obtain ⟨hyC, hyW⟩ := w3_list_mem y hy
    have hw := s134_pre_mem S hyC hyW
    have hcomm := s134_comm_V_conj S haVh (hV3Vh hw)
    have hfix : a * (S.frame.ψ.symm ⟨y, hyC⟩ : G) * a⁻¹ = S.frame.ψ.symm ⟨y, hyC⟩ := by
      rw [hcomm]
      group
    have h1 := (S.conj_eq_iff ⟨a, haN⟩ (S.frame.ψ.symm ⟨y, hyC⟩)).1 hfix
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val h1
    rwa [G6.coreAct_coe] at h2

  obtain ⟨hwV, hψw⟩ := s134_psi_comm S haN hv
  have hwVh : ⁅v, a⁆ ∈ Vh := by
    rw [commutatorElement_def]
    exact mul_mem (hVN v hv a haVh) (inv_mem haVh)
  have hwe : (S.frame.ψ ⟨⁅v, a⁆, hwV⟩ : P6) = e45 := by
    rw [hψw]
    rcases w3_fix _ haK hfixW _ (S.frame.ψ ⟨v, hv⟩).2 with h0 | h0
    · exfalso
      apply hva
      have h1 : S.frame.ψ ⟨⁅v, a⁆, hwV⟩ = 1 := by
        apply Subtype.ext
        rw [hψw]
        exact h0
      have h2 := congrArg Subtype.val (S.frame.ψ.map_eq_one_iff.1 h1)
      simp only [Subgroup.coe_one] at h2
      calc v * a = ⁅v, a⁆ * (a * v) := by rw [commutatorElement_def]; group
        _ = a * v := by rw [h2, one_mul]
    · exact h0

  have hzV : S.zV ∈ Vh := by
    have h0 := s134_pre_mem S e0123_mem (w3_list_mem _ e0123_mem_W3list).2
    have key : (⟨S.zV, S.zV_mem_V⟩ : ↥V) =
        S.frame.ψ.symm ⟨e0123, e0123_mem⟩ * ⟨⁅v, a⁆, hwV⟩ := by
      apply S.frame.ψ.injective
      apply Subtype.ext
      rw [S.psi_zV, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, hwe]
      exact allOnes_eq_mul
    have heq := congrArg Subtype.val key
    simp only [Subgroup.coe_mul] at heq
    rw [heq]
    exact mul_mem (hV3Vh h0) hwVh
  have hVeq := NQS134.eq_of_zV_mem_F4 h331 h1222 S hzV
  apply hva
  rw [← hVh] at hVeq
  exact s134_comm_V S hv (hVeq ▸ haVh)

end CFSG.Quasithin.H13.U3
