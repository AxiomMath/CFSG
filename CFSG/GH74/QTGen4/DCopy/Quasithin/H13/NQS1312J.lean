module

public import CFSG.Quasithin.H13.NQS1312J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312H

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_sylow_lineH_F4
    (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V]
    (hH : QTH13 G T L) (hF : QTU3InternalFrame T L V z) {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k) :
    ∃ S : Subgroup G, IsSylowTwoOf S (lineH Φ) ∧ pCoreOf 2 (L ⊔ T) ≤ S ∧
      S ≤ normalizer (pCoreOf 2 (L ⊔ T) : Set G) ∧ S ≤ normalizer (L : Set G) ∧
      S ⊓ centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) ∧
      ∀ a ∈ S, ∀ b ∈ S, a ∉ pCoreOf 2 (L ⊔ T) → b ∉ pCoreOf 2 (L ⊔ T) →
        a⁻¹ * b ∈ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, hVe, hV64, hVQ, -, hLV, hTV, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, -, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF
  set H := lineH Φ with hHdef
  set M := normalizer (L : Set G) with hM
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hQT : Q ≤ T := hTC ▸ inf_le_left
  have hQM : Q ≤ M := hQT.trans hTL
  have hCVH : centralizer (V : Set G) ≤ H := by
    refine Subgroup.centralizer_le ?_
    rintro _ (rfl | rfl)
    exacts [ptOf_mem _, ptOf_mem _]
  have hQH : Q ≤ H := hQC.trans hCVH
  have hHu : H ≤ centralizer ({ptOf Φ (vecOf 15)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hHM : M ⊓ H ≤ normalizer (V : Set G) := fun x hx =>
    hTI _ (ptOf_mem _) ptOf_fifteen_ne_one ⟨hx.1, hHu hx.2⟩
  have hcen : ∀ x ∈ H, x * ptOf Φ (vecOf 15) * x⁻¹ = ptOf Φ (vecOf 15) ∧
      x * ptOf Φ (vecOf 52) * x⁻¹ = ptOf Φ (vecOf 52) := by
    intro x hx
    rw [hHdef, lineH, mem_centralizer_iff] at hx
    refine ⟨?_, ?_⟩
    · rw [← hx _ (Set.mem_insert _ _)]; group
    · rw [← hx _ (Set.mem_insert_of_mem _ rfl)]; group

  obtain ⟨S, hQS, hS⟩ := exists_isSylowTwoOf_of_le (le_inf hQM hQH) hQp
  have hSp : IsPGroup 2 S := hS.2.1
  have hSMH : S ≤ M ⊓ H := hS.1
  have hSN : S ≤ normalizer (V : Set G) := hSMH.trans hHM
  have hSQ : S ⊓ centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQS hQC)
    exact (eq_of_isSylowTwoOf_le (isSylowTwoOf_Q hH hF) (le_inf hQS hQC)
      (inf_le_inf_right _ (hSMH.trans inf_le_left)) (hSp.to_le inf_le_left)).le
  have hSnQ : S ≤ normalizer (Q : Set G) := by
    intro s hs
    rw [← hSQ]
    exact inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
      normalizer_le_normalizer_centralizer V (hSN hs)⟩

  have hact : ∀ a (ha : a ∈ S), ∃ κ : GL (Fin 6) (ZMod 2), tau Φ ⟨a, hSN ha⟩ = κ ∧ ∃ e ∈ c6List,
      (κ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e := by
    intro a ha
    obtain ⟨κ, -, hκ, e, he, hκe⟩ := exists_c6List_of_centralizes hΦN (hSN ha)
      (hcen a (hSMH ha).2).1 (hcen a (hSMH ha).2).2
    exact ⟨κ, tau_eq_iff.2 hκ, e, he, hκe⟩

  have hinv : ∀ a (ha : a ∈ S), a ∉ Q → ∃ e ∈ c6List,
      ((tau Φ ⟨a, hSN ha⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e ∧
        e ≠ id6 ∧ mul6 e e = id6 ∧
        ((Finset.range 64).filter (fun v => vapp e v = v)).card ≤ 16 := by
    intro a ha haQ
    obtain ⟨κ, hκ, e, he, hκe⟩ := hact a ha
    rw [hκ]
    rcases c6List_cases' e he with rfl | ⟨h3, hv⟩ | ⟨h2, hc⟩
    · exfalso
      apply haQ
      rw [← hSQ]
      refine ⟨ha, mem_centralizer_of_tau (Φ := Φ) (hSN ha) ?_⟩
      rw [hκ]
      exact Units.ext (by rw [hκe, colMat_id6, Units.val_one])
    · exact (false_of_tau_order_three hSp ha (hSN ha) (by rw [hκ]; exact hκe) h3 hv).elim
    · refine ⟨e, he, hκe, ?_, h2, hc⟩
      rintro rfl
      apply haQ
      rw [← hSQ]
      refine ⟨ha, mem_centralizer_of_tau (Φ := Φ) (hSN ha) ?_⟩
      rw [hκ]
      exact Units.ext (by rw [hκe, colMat_id6, Units.val_one])

  have hidx : ∀ a ∈ S, ∀ b ∈ S, a ∉ Q → b ∉ Q → a⁻¹ * b ∈ Q := by
    intro a ha b hb haQ hbQ
    obtain ⟨e, he, hae, he1, he2, -⟩ := hinv a ha haQ
    obtain ⟨e', he', hbe, he'1, he'2, -⟩ := hinv b hb hbQ
    have hab : a⁻¹ * b ∈ S := S.mul_mem (S.inv_mem ha) hb
    have hτ : tau Φ ⟨a⁻¹ * b, hSN hab⟩ = tau Φ ⟨a, hSN ha⟩ * tau Φ ⟨b, hSN hb⟩ := by
      have hsq : tau Φ ⟨a, hSN ha⟩ * tau Φ ⟨a, hSN ha⟩ = 1 :=
        Units.ext (by rw [Units.val_mul, hae, ← colMat_mul6, he2, colMat_id6, Units.val_one])
      have h1 : (⟨a⁻¹ * b, hSN hab⟩ : normalizer (V : Set G)) =
          (⟨a, hSN ha⟩ : normalizer (V : Set G))⁻¹ * ⟨b, hSN hb⟩ := rfl
      rw [h1, map_mul, map_inv, inv_eq_of_mul_eq_one_right hsq]
    by_cases hee : e = e'
    · subst hee
      rw [← hSQ]
      refine ⟨hab, mem_centralizer_of_tau (Φ := Φ) (hSN hab) ?_⟩
      rw [hτ]
      have : tau Φ ⟨a, hSN ha⟩ = tau Φ ⟨b, hSN hb⟩ := Units.ext (by rw [hae, hbe])
      rw [this]
      exact Units.ext (by rw [Units.val_mul, hbe, ← colMat_mul6, he'2, colMat_id6,
        Units.val_one])
    · obtain ⟨h3, hv⟩ := c6List_invol_mul e he e' he' he2 he'2 he1 he'1 hee
      exact (false_of_tau_order_three hSp hab (hSN hab)
        (by rw [hτ, Units.val_mul, hae, hbe, ← colMat_mul6]) h3 hv).elim

  have hVe' : IsElemAbelian 2 V := isElemAbelian_of_frame
  have hfix : ∀ a ∈ S, a ∉ Q →
      4 * Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ Nat.card V := by
    intro a ha haQ
    obtain ⟨e, he, hae, -, -, hc⟩ := hinv a ha haQ
    have h16 := card_inf_centralizer_le (hSN ha) (tau_eq_iff.1 rfl) hae (c6List_lt e he) hc
    rw [hV64]
    omega
  have hJ : thompsonJ S ≤ Q := thompsonJ_le_of_fix hVQ hQS hQC hVe' hidx hfix
  have hJeq : thompsonJ Q = thompsonJ S := GammaExtra.thompsonJ_eq_of_le hJ hQS

  have hJ1 : thompsonJ Q ≠ ⊥ := by
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian Q
    have h1 := hA.2.2 V hVQ hVe'
    rw [hV64] at h1
    intro h0
    have hA0 : A = ⊥ := le_bot_iff.1 (h0 ▸ GammaExtra.le_thompsonJ hA)
    rw [hA0, card_bot] at h1
    omega
  have hNJ : normalizer (thompsonJ Q : Set G) ≤ M :=
    normalizer_le_of_le_Q_F4 h1332 hH hJ1 (hQp.to_le (GammaExtra.thompsonJ_le_self Q))
      (GammaExtra.thompsonJ_le_self Q)
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
        (GammaExtra.normalizer_le_normalizer_thompsonJ Q))
  have hNS : normalizer (S : Set G) ≤ M := by
    have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ S
    rw [← hJeq] at h1
    exact h1.trans hNJ
  exact ⟨S, E6.isSylowTwoOf_of_normalizer_le hS (hSMH.trans inf_le_right)
    (hSMH.trans inf_le_left) hNS, hQS, hSnQ, hSMH.trans inf_le_left, hSQ, hidx⟩

end CFSG.Quasithin.H13.U3.NLine
