module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

theorem le_normalizer_component_of_centralizer_le {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {R X₀ : Subgroup X} (hR : IsPGroup p R)
    (hC : ∀ A : Subgroup X, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) →
      Subgroup.centralizer (A : Set X) ≤ X₀)
    {L : Subgroup X} (hL : IsComponentOf L ⊤) (hLX : ¬ L ≤ X₀)
    {u : X} (huR : u ∈ R) (huL : u ∈ L) (hup : orderOf u = p) (hunc : ∃ c ∈ L, u * c ≠ c * u) :
    R ≤ Subgroup.normalizer (L : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro r hr
  by_contra hrN
  set L₂ : Subgroup X := L.map (MulAut.conj r).toMonoidHom with hL₂
  set L₃ : Subgroup X := L.map (MulAut.conj (r ^ 2)).toMonoidHom with hL₃
  have hcomp : ∀ g : X, IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := fun g =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hmemN : ∀ g : X, L.map (MulAut.conj g).toMonoidHom = L →
      g ∈ Subgroup.normalizer (L : Set X) := by
    intro g hg
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [← hg]
    exact ⟨n, hn, rfl⟩
  have hrodd : Odd (orderOf r) := by
    obtain ⟨k, hk⟩ := (hR ⟨r, hr⟩)
    have : orderOf r ∣ p ^ k := by
      rw [← Subgroup.orderOf_mk r hr]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp this
    rw [hj]
    exact (hp.odd_of_ne_two hp2).pow
  have h12 : L ≠ L₂ := fun h => hrN (hmemN r h.symm)
  have h23 : L₂ ≠ L₃ := by
    intro h
    apply hrN
    apply hmemN r
    have h' := congrArg (fun K : Subgroup X => K.map (MulAut.conj r⁻¹).toMonoidHom) h
    simp only [hL₂, hL₃, Subgroup.map_map] at h'
    have e1 : (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj r).toMonoidHom = MonoidHom.id X := by
      ext x; simp; group
    have e2 : (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj (r ^ 2)).toMonoidHom =
        (MulAut.conj r).toMonoidHom := by
      ext x; simp [pow_two]; group
    rw [e1, e2, Subgroup.map_id] at h'
    exact h'.symm
  have h13 : L ≠ L₃ := by
    intro h
    apply hrN
    have hr2 : r ^ 2 ∈ Subgroup.normalizer (L : Set X) := hmemN (r ^ 2) h.symm
    obtain ⟨k, hk⟩ := hrodd
    have hrk : r = (r ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf r + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hrk]
    exact Subgroup.pow_mem _ hr2 _
  have hL₂c := hcomp r
  have hL₃c := hcomp (r ^ 2)
  set u₂ : X := r * u * r⁻¹ with hu₂
  set u₃ : X := r ^ 2 * u * (r ^ 2)⁻¹ with hu₃
  have hu₂R : u₂ ∈ R := R.mul_mem (R.mul_mem hr huR) (R.inv_mem hr)
  have hu₃R : u₃ ∈ R := R.mul_mem (R.mul_mem (R.pow_mem hr 2) huR) (R.inv_mem (R.pow_mem hr 2))
  have hu₂L : u₂ ∈ L₂ := ⟨u, huL, by simp [hu₂]⟩
  have hu₃L : u₃ ∈ L₃ := ⟨u, huL, by simp only [hu₃, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hu₂p : u₂ ^ p = 1 := by
    rw [hu₂, conj_pow, ← hup, pow_orderOf_eq_one]; group
  have hu₃p : u₃ ^ p = 1 := by
    rw [hu₃, conj_pow, ← hup, pow_orderOf_eq_one]; group
  have hup' : u ^ p = 1 := by rw [← hup, pow_orderOf_eq_one]
  obtain ⟨c, hcL, hcu⟩ := hunc
  have hu₃nc : ¬ ∀ l ∈ L₃, l * u₃ = u₃ * l := by
    intro h
    apply hcu
    have := h (r ^ 2 * c * (r ^ 2)⁻¹)
      ⟨c, hcL, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rw [hu₃] at this
    have key : r ^ 2 * (c * u) * (r ^ 2)⁻¹ = r ^ 2 * (u * c) * (r ^ 2)⁻¹ := by
      calc r ^ 2 * (c * u) * (r ^ 2)⁻¹ = (r ^ 2 * c * (r ^ 2)⁻¹) * (r ^ 2 * u * (r ^ 2)⁻¹) := by
            group
        _ = (r ^ 2 * u * (r ^ 2)⁻¹) * (r ^ 2 * c * (r ^ 2)⁻¹) := this
        _ = r ^ 2 * (u * c) * (r ^ 2)⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel key)).symm
  have hcomm₂ : ∀ x ∈ L₂, ∀ l ∈ L, x * l = l * x := fun x hx l hl =>
    (KFactProofs.K3.component_commute hL hL₂c h12 hl hx).symm
  have hcomm₃ : ∀ x ∈ L₃, ∀ l ∈ L, x * l = l * x := fun x hx l hl =>
    (KFactProofs.K3.component_commute hL hL₃c h13 hl hx).symm
  have hsupC : L₂ ⊔ L₃ ≤ Subgroup.centralizer (L : Set X) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro l hl
    · exact (hcomm₂ x hx l hl).symm
    · exact (hcomm₃ x hx l hl).symm
  have hE₁ : IsElemAbelian p (Subgroup.zpowers u₂) :=
    ⟨inferInstance, fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu₂p, one_zpow]⟩
  have hcard₁ : Nat.card (Subgroup.zpowers u₂) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hu₂p (by
      intro h
      apply hcu
      have h1 : u = 1 := by
        calc u = r⁻¹ * (r * u * r⁻¹) * r := by group
          _ = r⁻¹ * 1 * r := by rw [← hu₂, h]
          _ = 1 := by group
      rw [h1, one_mul, mul_one])
  have hu₃E₁ : u₃ ∉ Subgroup.zpowers u₂ := by
    intro h
    apply hu₃nc
    intro l hl
    have hu₃L₂ : u₃ ∈ L₂ := (Subgroup.zpowers_le.mpr hu₂L) h
    exact KFactProofs.K3.component_commute hL₃c hL₂c h23.symm hl hu₃L₂
  have hu₂u₃ : ∀ e ∈ Subgroup.zpowers u₂, e * u₃ = u₃ * e := fun e he =>
    KFactProofs.K3.component_commute hL₂c hL₃c h23 ((Subgroup.zpowers_le.mpr hu₂L) he) hu₃L
  obtain ⟨hA, hAcard⟩ :=
    CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hE₁ hcard₁ hu₃p hu₃E₁ hu₂u₃
  set A : Subgroup X := Subgroup.zpowers u₂ ⊔ Subgroup.zpowers u₃ with hAdef
  have hAR : A ≤ R := sup_le (Subgroup.zpowers_le.mpr hu₂R) (Subgroup.zpowers_le.mpr hu₃R)
  have hAL : A ≤ L₂ ⊔ L₃ :=
    sup_le ((Subgroup.zpowers_le.mpr hu₂L).trans le_sup_left)
      ((Subgroup.zpowers_le.mpr hu₃L).trans le_sup_right)
  have huA : u ∉ A := by
    intro h
    obtain ⟨c', hc'L, hc'⟩ : ∃ c' ∈ L, u * c' ≠ c' * u := ⟨c, hcL, hcu⟩
    apply hc'
    have := Subgroup.mem_centralizer_iff.mp (hsupC (hAL h)) c' hc'L
    exact this.symm
  have huAc : ∀ e ∈ A, e * u = u * e := fun e he =>
    (Subgroup.mem_centralizer_iff.mp (hsupC (hAL he)) u huL).symm
  obtain ⟨hE, hEcard⟩ :=
    CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hA hAcard hup' huA huAc
  have hEle : A ⊔ Subgroup.zpowers u ≤ R ⊓ Subgroup.centralizer (A : Set X) := by
    refine le_inf (sup_le hAR (Subgroup.zpowers_le.mpr huR)) ?_
    have hAc : A ≤ Subgroup.centralizer (A : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hA.1
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : A) ⟨x, hx⟩)
    refine sup_le hAc (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact huAc y hy
  have hrank : 3 ≤ CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) :=
    (three_le_pRank_of_card hp hE hEcard).trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hEle)
  apply hLX
  refine le_trans ?_ (hC A hAR hA hAcard hrank)
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hsupC (hAL ha)) l hl).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
