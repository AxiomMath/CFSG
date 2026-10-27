module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentCore
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoKill
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y} {K : Subgroup Y}

theorem mem_of_mem_centralizer (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K := fun c hc hcp =>
  mem_of_mem_centralizer_of_orderOf_eq Rb hKn
    (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp

theorem mem_center_of_mem_centralizer (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype := fun c hc hcp =>
  mem_map_center_of_mem_of_mem_centralizer (mem_of_mem_centralizer hKn hcent c hc hcp) hc

theorem isPGroup_centralizer (hred : ReducedNongeneration p Y Rb Y₀) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    IsPGroup p (Subgroup.centralizer (K : Set Y)) :=
  isPGroup_centralizer_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn
    (mem_of_mem_centralizer hKn hcent)

theorem isCyclic_centralizer (hred : ReducedNongeneration p Y Rb Y₀) (hK : IsComponentOf K ⊤)
    (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    IsCyclic (Subgroup.centralizer (K : Set Y)) :=
  isCyclic_centralizer_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn
    (mem_of_mem_centralizer hKn hcent) (hred.isCyclic_map_center hK hKn)

theorem centralizer_eq_bot (hred : ReducedNongeneration p Y Rb Y₀) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hZ : Subgroup.center K = ⊥) : Subgroup.centralizer (K : Set Y) = ⊥ :=
  centralizer_eq_bot_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn
    (mem_of_mem_centralizer hKn hcent) hZ

theorem isPGroup_center (hred : ReducedNongeneration p Y Rb Y₀) (hK : IsComponentOf K ⊤) :
    IsPGroup p (Subgroup.center K) :=
  isPGroup_center_of_isComponentOf hred.prime hred.core_eq_bot hK

theorem pRank_sylow_le_three (hrank : Open.pRank p (Rb : Subgroup Y) = 3) (T : Sylow p K) :
    Open.pRank p (T : Subgroup K) ≤ 3 := by
  have hp : p.Prime := Fact.out
  obtain ⟨S, hS⟩ := (T.isPGroup'.map K.subtype).exists_le_sylow
  calc Open.pRank p (T : Subgroup K)
      ≤ Open.pRank p ((T : Subgroup K).map K.subtype) :=
        SectionRank.pRank_le_map hp.one_lt K.subtype K.subtype_injective _
    _ ≤ Open.pRank p (S : Subgroup Y) := SectionRank.pRank_mono hp.one_lt hS
    _ = Open.pRank p (Rb : Subgroup Y) := sylow_pRank_eq p hp S Rb
    _ = 3 := hrank

theorem false_of_le_weakCore {T : Type*} [Group T] (hred : ReducedNongeneration p Y Rb Y₀)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (e : K ⧸ Subgroup.center K ≃* T)
    (hOut : ∀ S : Sylow p (Outer T), (S : Subgroup (Outer T)).Normal)
    (hW : K ≤ GLBWeakCore p (Rb : Subgroup Y)) : False := by
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hCR := IsPGroup.le_sylow_of_normal (isPGroup_centralizer hred hKn hcent) Rb
  exact false_of_le_of_normal_sup hred (hW.trans hred.weakCore_le)
    (normal_sup_of_outer K e Rb hCR hOut)

theorem not_sq_dvd_index_of_card_lt (K : Subgroup Y) [K.Normal]
    (h : Nat.card (Rb : Subgroup Y) < p ^ 2 * Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y)) :
    ¬ p ^ 2 ∣ K.index := by
  have hp : p.Prime := Fact.out
  intro hdvd
  have h1 : K.relIndex ((Rb : Subgroup Y) ⊔ K) * ((Rb : Subgroup Y) ⊔ K).index = K.index :=
    Subgroup.relIndex_mul_index le_sup_right
  rw [Subgroup.relIndex_sup_right] at h1
  have h2 : ((Rb : Subgroup Y) ⊔ K).index ∣ (Rb : Subgroup Y).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have h3 : Nat.Coprime (p ^ 2) ((Rb : Subgroup Y) ⊔ K).index := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    exact fun hd => Rb.not_dvd_index (hd.trans h2)
  rw [← h1] at hdvd
  have h4 : p ^ 2 ∣ K.relIndex (Rb : Subgroup Y) := h3.dvd_of_dvd_mul_right hdvd
  have h5 : K.relIndex (Rb : Subgroup Y) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h6 : p ^ 2 ≤ K.relIndex (Rb : Subgroup Y) := Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h4
  have h7 : Nat.card (K.subgroupOf (Rb : Subgroup Y)) * K.relIndex (Rb : Subgroup Y) =
      Nat.card (Rb : Subgroup Y) := Subgroup.card_mul_index _
  have h8 : Nat.card (K.subgroupOf (Rb : Subgroup Y)) =
      Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) := by
    rw [← Subgroup.card_map_of_injective (Rb : Subgroup Y).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h8] at h7
  have h9 : Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) * p ^ 2 ≤ Nat.card (Rb : Subgroup Y) :=
    h7 ▸ Nat.mul_le_mul_left _ h6
  rw [mul_comm] at h9
  omega

theorem index_dvd_of_card_mulAut_dvd (K : Subgroup Y) [K.Normal]
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) {m : ℕ}
    (hm : Nat.card (MulAut K) ∣ m * Nat.card K) : K.index ∣ m := by
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  have h1 : Nat.card Y ∣ Nat.card (MulAut K) := Subgroup.card_dvd_of_injective _ hinj
  rw [← Subgroup.index_mul_card K] at h1
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos (h1.trans hm)

theorem false_of_le_comm {E A : Subgroup Y} (hEcard : Nat.card E = p ^ 3)
    (hEZ : Nat.card (Subgroup.center E) = p) (hEA : E ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : False := by
  have hp : p.Prime := Fact.out
  have htop : Subgroup.center E = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hA _ (hEA g.2) _ (hEA z.2))
  rw [htop, Subgroup.card_top, hEcard] at hEZ
  have h1 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h1
  omega

theorem false_of_comm_of_klingen (hKn : K.Normal)
    (hC : IsCyclic (Subgroup.centralizer (K : Set Y)))
    (hidx : ¬ p ^ 2 ∣ (K ⊔ Subgroup.centralizer (K : Set Y)).index)
    (hcomm : ∀ a ∈ (Rb : Subgroup Y) ⊓ K, ∀ b ∈ (Rb : Subgroup Y) ⊓ K, a * b = b * a)
    (hkl : HasKlingenData p Rb Y₀) : False := by
  obtain ⟨E, D, L, hER, hEcard, hEexp, hEZ, -, -, -, -, -, -, -, e, hSL⟩ := hkl
  have : K.Normal := hKn
  have hEK : E ≤ K := le_of_klingen hC hidx hEcard hEexp hEZ e hSL
  exact false_of_le_comm hEcard hEZ (le_inf hER hEK) hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
