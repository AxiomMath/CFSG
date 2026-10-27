module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutLift
public import CFSG.RankThree.PartOne.KF.F128Act
public import CFSG.RankThree.PartOne.S11c.Sec66PSU

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem statedClassicalModel_of_surjective {Y : Type} [Group Y] (L : Subgroup Y)
    (hL : CFSG.Open.IsQuasisimple ↥L) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 2) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (π : SU (unitaryInvolution F 2 2) n →* ↥L ⧸ Subgroup.center ↥L) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 2) n)) :
    StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 2 := by
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  have : Group.IsPerfect ↥L := ⟨hL.1⟩
  have hP : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)
  have hcenter : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_perfect
      (by rw [← _root_.commutator_def]; exact hP.commutator_eq_top)
  have hZ : Subgroup.center (SU (unitaryInvolution F 2 2) n) ≤ π.ker := by
    intro z hz
    have : π z ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨s, rfl⟩ := hπ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
    rw [hcenter, Subgroup.mem_bot] at this
    exact this
  have hkerEq : π.ker = Subgroup.center (SU (unitaryInvolution F 2 2) n) :=
    le_antisymm hker hZ
  let e : SU (unitaryInvolution F 2 2) n ⧸ Subgroup.center (SU (unitaryInvolution F 2 2) n) ≃*
      ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hadm : StatedLieAdmissible .PSU n 2 2 :=
    ⟨Nat.prime_two, by norm_num, hn, fun h' => by
      have := (Prod.mk.inj h').2
      omega⟩
  exact statedClassicalModel_of_mulEquiv e (statedClassicalModel_center_quotient hadm hF)

theorem exists_fixed_of_model {T : Type} [Group T] {n : ℕ} (hn : 10 ≤ n)
    (hC : StatedClassicalModel T .PSU n 2 2) (α : MulAut T) (hα : α ^ 5 = 1)
    (hnin : α ∉ innerAut T) : ∃ y : T, α y = y ∧ (orderOf y = 13 ∨ orderOf y = 41) := by
  obtain ⟨K, _, _, hU, hn3, hq, ⟨e⟩⟩ := psu_prime_form_model hC
  have hα' : MulAut.congr e α ^ 5 = 1 := by rw [← map_pow, hα, map_one]
  have hnin' : MulAut.congr e α ∉
      innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hm => hnin ((mem_innerAut_congr e α).1 hm)
  obtain ⟨y', hy', hord⟩ := exists_fixed_prime_order hU hn _ hα' hnin'
  refine ⟨e.symm y', ?_, ?_⟩
  · have h1 : e (α (e.symm y')) = y' := hy'
    have h2 := congrArg e.symm h1
    rwa [e.symm_apply_apply] at h2
  · rw [MulEquiv.orderOf_eq]
    exact hord

theorem diagLeviBad : DiagLeviBad := by
  intro Y _ _ L J hL hcl hpar hne hnB n F _ _ _ hF he h5 π hπ hker hlast x hx hxp hxo hN hfix
  exfalso
  have : Finite (SU (unitaryInvolution F 2 2) n) := Finite.of_injective _ Subtype.val_injective
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hs : Subsingleton (SU (unitaryInvolution F 2 2) 0) :=
      ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
    obtain ⟨a, b, hab⟩ :=
      (IsSimpleGroup.toNontrivial (G := ↥L ⧸ Subgroup.center ↥L)).exists_pair_ne
    obtain ⟨s, rfl⟩ := hπ a
    obtain ⟨t, rfl⟩ := hπ b
    exact hab (by rw [Subsingleton.elim s t])
  have hn10 : 10 ≤ n := by
    obtain ⟨k, hk⟩ := he
    omega
  have hmodel := statedClassicalModel_of_surjective L hLq hF (by omega) π hπ hker
  obtain ⟨nW, H, hB⟩ := borelQuotient_su_of_surjective (hF := hF) (n := n) (by omega)
    (fun h' => by have := (Prod.mk.inj h').1; omega) π hπ hker
  have hM : Nat.card F - 1 = 15 := by rw [hF]; norm_num
  have : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hα5 : centerQuotientConj L ⟨x, hx⟩ ^ 5 = 1 := centerQuotientConj_pow hx hxp
  have hαnin : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L) :=
    fun hm => hxo ((centerQuotientConj_mem_innerAut_iff this hx).1 hm)
  obtain ⟨y, hy, hord⟩ := exists_fixed_of_model hn10 hmodel _ hα5 hαnin
  have hdvd : ∀ r : ℕ, r.Prime → Nat.Coprime r 5 → orderOf y = r →
      r ∣ Nat.card ↥(quotImage L J) := by
    intro r hr hr5 hyr
    have hyr' : y ^ r = 1 := hyr ▸ pow_orderOf_eq_one y
    have hyJ := mem_quotImage_of_coprime L J hx (p := 5) (by norm_num) hxp hfix hy hr5 hyr'
    have := orderOf_dvd_natCard (⟨y, hyJ⟩ : ↥(quotImage L J))
    rwa [Subgroup.orderOf_mk, hyr] at this
  rcases hord with h13 | h41
  · exact hlast.not_dvd_card_of_seven_le hB rfl he (by norm_num) (by norm_num)
      (by rw [hM]; norm_num) (hdvd 13 (by norm_num) (by norm_num) h13)
  · exact hlast.not_dvd_card_of_seven_le hB rfl he (by norm_num) (by norm_num)
      (by rw [hM]; norm_num) (hdvd 41 (by norm_num) (by norm_num) h41)

end CFSG.AGLEmbedding.LieOut
