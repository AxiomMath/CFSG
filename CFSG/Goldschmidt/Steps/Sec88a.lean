module

public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.Steps.Ppp
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec87d
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.Walter.Bender1970.S38.Basic

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem facts81 (h81 : S_G81) (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {b : G}
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ∈ Walter.benderM b ∧
      Subgroup.centralizer ({b} : Set G) =
        oddCoreOf (Subgroup.centralizer ({b} : Set G)) ⊔ Subgroup.centralizer (A : Set G) ∧
      ⁅A, oddCoreOf (Subgroup.centralizer ({b} : Set G))⁆ ≠ ⊥ ∧
      normalClosureIn (Subgroup.centralizer ({b} : Set G)) A =
        oddCoreOf (normalClosureIn (Subgroup.centralizer ({b} : Set G)) A) ⊔ A := by
  obtain ⟨H, hH⟩ := G73.benderM_nonempty hset hb1
  obtain ⟨hHb, hHO, hAO, -⟩ := h81 G S A hset h4 b hb hb1 H hH
  subst hHb
  exact ⟨hH, hHO, hAO, (eq_oddCoreOf_sup hset h4 hb hb1 hH).1⟩

theorem isGood_of_mem (h81 : S_G81) (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) : Ppp.IsGood A a :=
  Ppp.isGood_of_normalClosureIn_eq (S.isPGroup'.to_le hset.le)
    (fun _ hc => Subgroup.mem_centralizer_singleton_iff.mpr (comm hset.elem hc ha))
    (facts81 h81 hset h4 ha ha1).2.2.2

theorem mem_normalizer_commSpan {g : G}
    (hg : ∀ a ∈ A, a ≠ 1 → ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆.map
      (MulAut.conj g).toMonoidHom = ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) :
    g ∈ Subgroup.normalizer ((Ppp.commSpan A : Subgroup G) : Set G) := by
  rw [← Walter.map_conj_eq_iff_mem_normalizer, Ppp.commSpan, Subgroup.map_iSup]
  refine iSup_congr fun a => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun ha => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun ha1 => hg a ha ha1

theorem false_of_odd_commSpan (h81 : S_G81) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hodd : Odd (Nat.card (Ppp.commSpan A))) : False := by
  have hsimple := hset.isSimpleGroup
  set Y := Ppp.commSpan A with hY
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hset.le
  have hCY : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    intro c hc
    refine mem_normalizer_commSpan fun a ha ha1 => ?_
    have hcA : A.map (MulAut.conj c).toMonoidHom = A :=
      Walter.map_conj_eq_iff_mem_normalizer.mpr (Subgroup.centralizer_le_normalizer _ hc)
    have hcO : (oddCoreOf (Subgroup.centralizer ({a} : Set G))).map (MulAut.conj c).toMonoidHom =
        oddCoreOf (Subgroup.centralizer ({a} : Set G)) :=
      Walter.map_conj_eq_iff_mem_normalizer.mpr (le_normalizer_oddCoreOf _
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) hc))
    rw [Subgroup.map_commutator, hcA, hcO]
  have hNY : ∀ b ∈ A, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer (Y : Set G) := by
    intro b hb hb1
    obtain ⟨-, hbO, -, -⟩ := facts81 h81 hset h4 hb hb1
    rw [hbO]
    refine sup_le ?_ hCY
    set O := oddCoreOf (Subgroup.centralizer ({b} : Set G)) with hO
    have hAO : A ≤ Subgroup.normalizer (O : Set G) := fun c hc =>
      le_normalizer_oddCoreOf _ (Subgroup.mem_centralizer_singleton_iff.mpr (comm hset.elem hc hb))
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
      Nat.prime_two A O hA2 hAO (Nat.coprime_two_left.mpr (odd_card_oddCoreOf _))
    rw [← hfac]
    refine sup_le ?_ (inf_le_right.trans hCY)
    refine le_trans ?_ (Subgroup.le_normalizer : Y ≤ _)
    exact le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))
  have htop : Subgroup.normalizer (Y : Set G) = ⊤ := by
    by_contra hne
    exact false_of_centralizer_le hset hne hNY
  have hYO : Y ≤ oddCoreOf (⊤ : Subgroup G) :=
    le_oddCoreOf le_top (top_le_iff.mpr htop) hodd
  rw [oddCoreOf_top_eq_bot hset, le_bot_iff] at hYO
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  apply (facts81 h81 hset h4 ha ha1).2.2.1
  rw [Subgroup.commutator_comm, ← le_bot_iff, ← hYO]
  exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

theorem exists_not_isGood (h81 : S_G81) (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {t : G}
    (htS : t ∈ (S : Subgroup G)) (ht2 : t ^ 2 = 1) (htA : t ∉ A) :
    ∃ a₀ ∈ A, ¬ Ppp.IsGood A (t * a₀) := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  refine false_of_odd_commSpan h81 hset h4 (Ppp.odd_card_commSpan' hset.elem h4.ge ht2 htA
    (le_centralizer hset h4 htS) (fun a ha ha1 => isGood_of_mem h81 hset h4 ha ha1) hall)

end CFSG.Goldschmidt.Sec8
