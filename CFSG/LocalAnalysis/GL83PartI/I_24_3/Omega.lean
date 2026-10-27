module

public import CFSG.Open.GLBDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GL83PartI.I_22_6.Center
import CFSG.LocalAnalysis.GL83PartI.I_24_3.OmegaAux
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace GL83.I243

open CFSG CFSG.Open

theorem omega_le_zpowers_of_not_le_weakCore
    {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (R : Sylow p X)
    {B K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKR : ¬ K ≤ GLBWeakCore p (R : Subgroup X))
    (hBR : B ≤ (R : Subgroup X)) (hBel : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ Open.pRank p (R : Subgroup X))
    (hB3 : 3 ≤ Open.pRank p (R : Subgroup X))
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    {z : X} (hzB : z ∈ B) (hzK : z ∈ K) (hzc : z ∈ Subgroup.centralizer (K : Set X))
    (hzp : orderOf z = p)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z) :
    ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro c hcK hcc hcp
  by_contra hcz
  have hKsub : K.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.mp hK.2.1
  have hcentr : ∀ g : X, g ∈ Subgroup.centralizer (K : Set X) ↔ ∀ w ∈ K, g * w = w * g :=
    fun g => by
      rw [Subgroup.mem_centralizer_iff]
      exact ⟨fun h w hw => (h w hw).symm, fun h w hw => (h w hw).symm⟩
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
    have := hBel.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : B) ⟨b, hb⟩)
  have hzp1 : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
  let V : Subgroup X := GL83.CompFam.torsionCentre p K
  have hmemV : ∀ v : X, v ∈ V ↔ v ∈ K ∧ (∀ w ∈ K, v * w = w * v) ∧ v ^ p = 1 :=
    fun v => GL83.CompFam.mem_torsionCentre
  have hcV : c ∈ V := (hmemV c).2 ⟨hcK, (hcentr c).1 hcc, hcp⟩
  have hzV : z ∈ V := (hmemV z).2 ⟨hzK, (hcentr z).1 hzc, hzp1⟩
  have hVel : IsElemAbelian p V :=
    ⟨⟨⟨fun a b => Subtype.ext (((hmemV a).1 a.2).2.1 b ((hmemV b).1 b.2).1)⟩⟩,
      fun x hx => ((hmemV x).1 hx).2.2⟩
  have hBV : ∀ b ∈ B, ∀ v ∈ V, b * v * b⁻¹ ∈ V := fun b hb v hv =>
    GL83.CompFam.conj_mem_torsionCentre
      (GL83.CompFam.cj_eq_iff_mem_normalizer.mpr (hBN hb)) hv
  have hzcomm : ∀ b ∈ B, ∀ n ∈ Subgroup.zpowers z, b * n * b⁻¹ = n := fun b hb n hn => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.zpow_right (hBcomm b hb z hzB) k).eq
  have hlt : Subgroup.zpowers z < V :=
    lt_of_le_of_ne (Subgroup.zpowers_le.mpr hzV) fun h => hcz (h ▸ hcV)
  obtain ⟨w, hwV, hwz, hw⟩ := exists_mem_not_mem_conj_mem (p := p) hBel.isPGroup hVel.isPGroup
    hBV (fun b hb n hn => (hzcomm b hb n hn).symm ▸ hn) hlt
  obtain ⟨hwK, hwc, hwp⟩ := (hmemV w).1 hwV
  have hwR : w ∈ (R : Subgroup X) :=
    mem_sylow_of_mem_of_commute_of_isSubnormal R hKsub hwK (fun k hk => (hwc k hk).symm) hwp
  have hwcen : w ∈ Subgroup.centralizer (K : Set X) := (hcentr w).2 hwc
  have hwB : w ∉ B := fun h => hwz (hCB w h hwcen)
  let B₀ : Subgroup X := B ⊓ Subgroup.centralizer ({w} : Set X)
  have hB₀B : B₀ ≤ B := inf_le_left
  have hwB₀ : ∀ b ∈ B₀, b * w = w * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp hb.2
  obtain ⟨hE, b, a, hba, hb, ha⟩ := isElemAbelian_sup_zpowers_and_exists_card hp
    (hBel.mono hB₀B) hwp hwB₀ fun h => hwB (hB₀B h)
  have hindex := card_le_mul_card_inf_centralizer_of_mem_zpowers hzp
    (fun b hb => hBcomm b hb z hzB) hw
  have hE3 : 3 ≤ Open.pRank p (B₀ ⊔ Subgroup.zpowers w) := by
    have h1 : p ^ Open.pRank p (R : Subgroup X) ≤ p ^ (b + 1) := by
      rw [← hBcard, pow_succ, mul_comm, ← hb]
      exact hindex
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have h3 : a ≤ Open.pRank p (B₀ ⊔ Subgroup.zpowers w) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE ha
    omega
  have hER : B₀ ⊔ Subgroup.zpowers w ≤ (R : Subgroup X) :=
    sup_le (hB₀B.trans hBR) (Subgroup.zpowers_le.mpr hwR)
  have hzw : z * w = w * z := (hwc z hzK).symm
  obtain ⟨-, hQ2⟩ := isElemAbelian_zpowers_sup_zpowers_and_two_le_pRank hp hzp hwp hzw hwz
  have hzB₀ : z ∈ B₀ := ⟨hzB, Subgroup.mem_centralizer_singleton_iff.mpr hzw⟩
  have hQE : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ B₀ ⊔ Subgroup.zpowers w :=
    sup_le_sup_right (Subgroup.zpowers_le.mpr hzB₀) _
  have hN := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore_of_commutative_overgroup p hp
    hER hQE hE.1 hQ2 hE3
  have hQK : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ Subgroup.centralizer (K : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr hzc) (Subgroup.zpowers_le.mpr hwcen)
  exact hKR ((Subgroup.le_centralizer_iff.mp hQK).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN))

end GL83.I243
