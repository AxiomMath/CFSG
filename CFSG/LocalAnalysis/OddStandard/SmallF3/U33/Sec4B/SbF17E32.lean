module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17Cy
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem isElemAbelian_zpowers_of_sq {a : G} (ha : a ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers a) := by
  have haz : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact ha
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    show (x : G) ^ 2 = 1
    rw [← hm, pow_two, ← zpow_add, show m + m = 2 * m by ring, zpow_mul a 2 m, haz, one_zpow]

private theorem isElemAbelian_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    CFSG.Open.IsElemAbelian 2 (closure ({a, b} : Set G)) := by
  have ha2 : a ^ 2 = 1 := by rwa [pow_two]
  have hb2 : b ^ 2 = 1 := by rwa [pow_two]
  have heq : closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  rw [heq]
  refine isElemAbelian_sup (isElemAbelian_zpowers_of_sq ha2)
    (isElemAbelian_zpowers_of_sq hb2) ?_
  intro x hx y hy
  rw [Subgroup.mem_zpowers_iff] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq

private theorem isElemAbelian_mono {H K : Subgroup G} (hH : CFSG.Open.IsElemAbelian 2 H)
    (hKH : K ≤ H) : CFSG.Open.IsElemAbelian 2 K := by
  haveI : IsMulCommutative ↥H := hH.1
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val (mul_comm' (⟨(a : G), hKH a.2⟩ : H) (⟨(b : G), hKH b.2⟩ : H))
  · intro x hx
    exact hH.2 x (hKH hx)

private theorem isElemAbelian_ctxYq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    exact IsZ4Z4E4.comm hc.q_iso ((mem_ctxYq_iff hc.q_iso a).mp a.2).1
      ((mem_ctxYq_iff hc.q_iso b).mp b.2).1
  · intro x hx
    exact ((mem_ctxYq_iff hc.q_iso x).mp hx).2

theorem l17_E32 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∃ B : Subgroup G, closure ({tau, om, lam} : Set G) ≤ B ∧
      CFSG.Open.IsElemAbelian 2 B ∧ 32 ≤ Nat.card B := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc
  have hom_tau : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have htau_om : tau * om = om * tau := hom_tau.symm
  let A0 : Subgroup G := closure ({tau, om} : Set G)
  let Y : Subgroup G := ctxYq t tau x₁ x₂ rho
  let C0 : Subgroup G := Y ⊓ centralizer ({lam} : Set G)
  let B1 : Subgroup G := A0 ⊔ C0
  have hA0mem : ∀ x : G, x ∈ A0 ↔ x = 1 ∨ x = tau ∨ x = om ∨ x = tau * om := by
    intro x
    dsimp [A0]
    exact mem_closure_pair_of_invol (by rw [← pow_two]; exact htau2)
      (by rw [← pow_two]; exact hom2) htau_om
  have hA0card : Nat.card A0 = 4 := by
    dsimp [A0]
    exact card_closure_pair htau2 (fun h1 => htau_not (by rw [h1]; exact Subgroup.one_mem _))
      hom2 htau_om (fun hmem => hc.om_not_mem
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp : tau ∈ ({t, tau} : Set G))))
          hmem))
  have hA0Q : A0 ⊓ ctxQ t tau x₁ x₂ rho = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgA, hgQ⟩ := Subgroup.mem_inf.mp hg
    rcases (hA0mem g).mp hgA with h | h | h | h
    · rw [h]; exact Subgroup.mem_bot.mpr rfl
    · exact absurd (h ▸ hgQ) (Ctx13.tau_not_mem_Q hc)
    · exact absurd (h ▸ hgQ) (Ctx13.om_not_mem_Q hc)
    · rw [h, htau_om] at hgQ
      exact absurd hgQ (Ctx13.omtau_not_mem_Q hc)
  have hC0Q : C0 ≤ ctxQ t tau x₁ x₂ rho := (inf_le_left : C0 ≤ Y).trans ctxYq_le_ctxQ
  have hA0C0 : A0 ⊓ C0 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgQ : g ∈ ctxQ t tau x₁ x₂ rho := hC0Q hgC
    have hmem : g ∈ A0 ⊓ ctxQ t tau x₁ x₂ rho := Subgroup.mem_inf.mpr ⟨hgA, hgQ⟩
    rwa [hA0Q] at hmem
  have hA0centY : A0 ≤ centralizer ((Y : Subgroup G) : Set G) := by
    dsimp [A0]
    rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({tau, om} : Set G))
    rcases ha with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hc.tau_cent_Y y hy).symm)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hc.om_cent_Y y hy).symm)
  have hC0centY : C0 ≤ centralizer ((Y : Subgroup G) : Set G) := by
    intro c hcY
    have hcY' : c ∈ Y := (Subgroup.mem_inf.mp hcY).1
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact (IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ hcY') (ctxYq_le_ctxQ hy)).symm
  have hnorm : ∀ k ∈ A0, ∀ h ∈ C0, k * h * k⁻¹ ∈ C0 := by
    intro k hk h hh
    have hhY : h ∈ Y := (Subgroup.mem_inf.mp hh).1
    have hcomm : k * h = h * k :=
      (Subgroup.mem_centralizer_iff.mp (hA0centY hk) h hhY).symm
    have hkh : k * h * k⁻¹ = h := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hkh]; exact hh
  have hcardC0 : Nat.card C0 = 4 := by
    simpa [C0, Y] using l17_card_CY_lam hc
  have hB1card : Nat.card B1 = 16 := by
    have h := card_sup_eq_mul (H := C0) (K := A0) hnorm (by rw [inf_comm]; exact hA0C0)
    rw [sup_comm] at h
    dsimp [B1]
    rw [h, hcardC0, hA0card]
  have hB1centY : B1 ≤ centralizer ((Y : Subgroup G) : Set G) := by
    dsimp [B1]
    exact sup_le hA0centY hC0centY
  have hlamB1 : B1 ≤ centralizer ({lam} : Set G) := by
    dsimp [B1]
    refine sup_le ?_ ?_
    · dsimp [A0]
      rw [Subgroup.closure_le]
      rintro a (ha : a ∈ ({tau, om} : Set G))
      rcases ha with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (l17_lam_comm hc).2.1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (l17_lam_comm hc).2.2.symm
    · intro c hcC
      exact (Subgroup.mem_inf.mp hcC).2
  have hcomm_lam : ∀ x ∈ B1, x * lam = lam * x :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hlamB1 hx)
  have hlam2 : lam ^ 2 = 1 := by
    rw [← hc.wreath.ord_lam]
    exact pow_orderOf_eq_one lam
  have hlam_notB1 : lam ∉ B1 := by
    intro hlamB1'
    have hlamCentY : lam ∈ centralizer ((Y : Subgroup G) : Set G) := hB1centY hlamB1'
    have hyY : x₁ ^ 2 ∈ Y := by
      dsimp [Y]
      exact l17_V_le_Y hc
        (Subgroup.subset_closure (by simp : x₁ ^ 2 ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G)))
    have hcomm' : x₁ ^ 2 * lam = lam * x₁ ^ 2 :=
      Subgroup.mem_centralizer_iff.mp hlamCentY (x₁ ^ 2) hyY
    have hly := l17_lam_y hc
    have h1 : lam * x₁ ^ 2 = x₁ ^ 2 * ((x₁ * x₂) ^ 2 * lam) := by
      calc lam * x₁ ^ 2 = (lam * x₁ ^ 2 * lam⁻¹) * lam := by group
        _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam := by rw [hly]
        _ = x₁ ^ 2 * ((x₁ * x₂) ^ 2 * lam) := by group
    have h2 : x₁ ^ 2 * lam = x₁ ^ 2 * ((x₁ * x₂) ^ 2 * lam) := by rw [hcomm', h1]
    have h3 : lam = (x₁ * x₂) ^ 2 * lam := mul_left_cancel h2
    exact (l17_yz_ne hc).2.1 (by
      have h4 : (1 : G) * lam = (x₁ * x₂) ^ 2 * lam := by rw [one_mul]; exact h3
      exact (mul_right_cancel h4).symm)
  have hBcard : Nat.card ↥(B1 ⊔ zpowers lam) = 2 * Nat.card B1 :=
    card_sup_zpowers_of_commute hlam2 hlam_notB1 hcomm_lam
  have hA0leB : A0 ≤ B1 ⊔ zpowers lam := (le_sup_left : A0 ≤ B1).trans le_sup_left
  have hZleB : zpowers lam ≤ B1 ⊔ zpowers lam := le_sup_right
  refine ⟨B1 ⊔ zpowers lam, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with h | h | h
    · rw [h]; exact hA0leB (Subgroup.subset_closure (by simp))
    · rw [h]; exact hA0leB (Subgroup.subset_closure (by simp))
    · rw [h]; exact hZleB (Subgroup.mem_zpowers lam)
  · have hA0elem : CFSG.Open.IsElemAbelian 2 A0 := by
      dsimp [A0]
      exact isElemAbelian_closure_pair (by rw [← pow_two]; exact htau2)
        (by rw [← pow_two]; exact hom2) htau_om
    have hC0elem : CFSG.Open.IsElemAbelian 2 C0 :=
      isElemAbelian_mono (isElemAbelian_ctxYq hc) (show C0 ≤ Y from inf_le_left)
    have hA0C0comm : ∀ a ∈ A0, ∀ c ∈ C0, a * c = c * a := by
      intro a ha c hcC
      have hcY : c ∈ Y := (Subgroup.mem_inf.mp hcC).1
      exact (Subgroup.mem_centralizer_iff.mp (hA0centY ha) c hcY).symm
    have hB1elem : CFSG.Open.IsElemAbelian 2 B1 := by
      dsimp [B1]
      exact isElemAbelian_sup hA0elem hC0elem hA0C0comm
    have hZelem : CFSG.Open.IsElemAbelian 2 (zpowers lam) :=
      isElemAbelian_zpowers_of_sq hlam2
    refine isElemAbelian_sup hB1elem hZelem ?_
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (show Commute x lam from hcomm_lam x hx).zpow_right j
  · rw [hBcard, hB1card]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
