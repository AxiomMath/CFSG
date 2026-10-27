module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Module
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

section Block

variable {L : Subgroup G} {n : ℕ}

theorem blockU_le_L (h : IsShort2 L) : blockU L ≤ L :=
  (C1.blockU_le_blockQ h).trans (C1.blockQ_le L)

theorem isElemAbelian_blockU (h : IsShort2 L) : IsElemAbelian 2 (blockU L) :=
  ⟨⟨⟨fun a b => Subtype.ext (C1.blockU_comm h _ a.2 _ (C1.blockU_le_blockQ h b.2))⟩⟩,
    fun x hx => h.2.2.1.2 x hx⟩

theorem card_blockU (hl : IsLin2Type L n) (hZ : blockZ L = ⊥) :
    Nat.card (blockU L) = 2 ^ (2 * n) := by
  have h := lin2_card_U hl
  rwa [hZ, Subgroup.card_bot, mul_one] at h

theorem not_isSolvable (hl : IsLin2Type L n) (hn : 2 ≤ n) : ¬ Group.IsSolvable ↥L := by
  obtain ⟨F, _, _, hF, α, hα, -⟩ := hl
  intro hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have hcp : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hFc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have hnab := Vol2Native.A312L.sl2_nonabelian hK4
  have hsimple := Vol2Native.A312L.sl2_isSimple hK4
  have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective hα
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem prime_dvd_card_L (hl : IsLin2Type L n) {ℓ : ℕ} (hℓ : ℓ ∣ 2 ^ (2 * n) - 1) :
    ℓ ∣ Nat.card L := by
  rw [lin2_card_L hl]
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
  rw [← pow_mul, mul_comm n 2]
  exact hℓ

theorem exists_orderOf_eq_prime [Finite G] (hl : IsLin2Type L n) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ 2 ^ (2 * n) - 1) : ∃ x ∈ L, orderOf x = ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite L := inferInstance
  have : Fintype L := Fintype.ofFinite L
  have hdvd' : ℓ ∣ Fintype.card L := by
    rw [← Nat.card_eq_fintype_card]
    exact prime_dvd_card_L hl hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card ℓ hdvd'
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem prime_dvd_card_of_le [Finite G] {K : Subgroup G} (hl : IsLin2Type L n) (hLK : L ≤ K)
    {ℓ : ℕ} (hℓ : ℓ ∣ 2 ^ (2 * n) - 1) : ℓ ∣ Nat.card K :=
  (prime_dvd_card_L hl hℓ).trans (Subgroup.card_dvd_of_le hLK)

end Block

end CFSG.QuasithinUnique.Lin2.OddRank
