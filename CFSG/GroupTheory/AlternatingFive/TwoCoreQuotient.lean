module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Alt

public section

namespace CFSG.GroupTheory.AlternatingFive

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem monoidHom_eq_one_of_isL2Quot_of_card_lt_sixty
    {L M : Type} [Group L] [Finite L] [Group M] [Finite M]
    (hquot : IsL2Quot 2 (oTwoQuot L)) (f : L →* M) (hM : Nat.card M < 60)
    (hQ : CFSG.pCore 2 L ≤ f.ker) : f = 1 := by
  classical
  haveI : IsSimpleGroup (oTwoQuot L) := by
    obtain ⟨e⟩ := hquot
    haveI : IsSimpleGroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
        (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num)
    exact e.isSimpleGroup
  let bar : oTwoQuot L →* M := QuotientGroup.lift (CFSG.pCore 2 L) f hQ
  have h60 : Nat.card (oTwoQuot L) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) hquot]
    norm_num
  have hbar : bar = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal bar.ker with hbot | htop
    · have hinj : Function.Injective bar := (MonoidHom.ker_eq_bot_iff bar).mp hbot
      have hle : Nat.card (oTwoQuot L) ≤ Nat.card M :=
        Nat.card_le_card_of_injective bar hinj
      omega
    · exact MonoidHom.ker_eq_top_iff.mp htop
  have hcomp : bar.comp (QuotientGroup.mk' (CFSG.pCore 2 L)) = f := rfl
  have hbar' : bar.comp (QuotientGroup.mk' (CFSG.pCore 2 L)) = 1 := by
    rw [hbar]
    rfl
  rwa [hcomp] at hbar'

theorem exists_orderOf_eq_three_of_isL2Quot [Finite G]
    {L : Subgroup G} (h : IsL2Quot 2 (oTwoQuot ↥L)) : ∃ x ∈ L, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) h]
    norm_num
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  have h3dvd : 3 ∣ Nat.card ↥L := by
    rw [hcard, h60]
    exact (show (3 : ℕ) ∣ 60 by norm_num).trans (dvd_mul_right 60 _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem mem_pCoreOf_of_forall_commutator_mem {L : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) {c : G} (hcL : c ∈ L)
    (h : ∀ l ∈ L, ⁅c, l⁆ ∈ pCoreOf 2 L) : c ∈ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)
  have hcent : π ⟨c, hcL⟩ ∈ Subgroup.center (oTwoQuot ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (N := CFSG.Open.pCore 2 ↥L) g
    have hcomm : ⁅π ⟨c, hcL⟩, π l⁆ = 1 := by
      rw [← map_commutatorElement]
      have hcoe : ((⁅(⟨c, hcL⟩ : ↥L), l⁆ : ↥L) : G) = ⁅c, (l : G)⁆ := by
        simp [commutatorElement_def]
      exact (QuotientGroup.eq_one_iff _).mpr
        ((F1.mem_pCore_iff_coe ⁅(⟨c, hcL⟩ : ↥L), l⁆).mpr
          (by rw [hcoe]; exact h (l : G) l.2))
    have hcomm' : ⁅π l, π ⟨c, hcL⟩⁆ = 1 := by
      simpa [commutatorElement_def, mul_assoc] using congrArg Inv.inv hcomm
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm'
  have hZ : Subgroup.center (oTwoQuot ↥L) = ⊥ := by
    obtain ⟨e⟩ := hq
    exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  rw [hZ, Subgroup.mem_bot] at hcent
  have hmem : (⟨c, hcL⟩ : ↥L) ∈ CFSG.Open.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff _).mp hcent
  exact (F1.mem_pCore_iff_coe ⟨c, hcL⟩).mp hmem

theorem exists_conjugator_mod_pCore {L : Subgroup G}
    (e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : orderOf x = 3) :
    ∃ g ∈ L, ∀ l ∈ L, x * l * x⁻¹ * (g * l * g⁻¹)⁻¹ ∈ pCoreOf 2 L := by
  classical
  let M : Subgroup G := Subgroup.normalizer (L : Set G)
  let φ : MulAut (oTwoQuot ↥L) := CFSG.GroupTheory.conjModPCore 2 L M le_rfl ⟨x, hxN⟩
  have hx3pow : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hxM3 : (⟨x, hxN⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa [M] using hx3pow)
  have hφ3 : φ ^ 3 = 1 := by
    have h := map_pow (CFSG.GroupTheory.conjModPCore 2 L M le_rfl) (⟨x, hxN⟩ : ↥M) 3
    rw [hxM3, map_one] at h
    simpa [φ] using h.symm
  have hford : orderOf φ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hφ3
  have hφodd : Odd (orderOf φ) := Odd.of_dvd_nat (by norm_num) hford
  obtain ⟨gbar, hgbar⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.L121.exists_conj_of_odd (Or.inl rfl) e φ hφodd
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨gL, hgL⟩ := hπsurj gbar
  refine ⟨(gL : G), gL.2, fun l hl => ?_⟩
  let lL : ↥L := ⟨l, hl⟩
  let xL : ↥L := ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN l).mp hl⟩
  let gl : ↥L := ⟨(gL : G) * l * (gL : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer gL.2) l).mp hl⟩
  have hφl : φ (π lL) = π xL := by
    simp only [φ, π, M, QuotientGroup.mk'_apply]
    rw [CFSG.GroupTheory.conjModPCore_mk]
  have hgl_eq : gl = gL * lL * gL⁻¹ := by
    apply Subtype.ext
    simp [gl, lL]
  have hπgl : π gl = π gL * π lL * (π gL)⁻¹ := by
    rw [hgl_eq, map_mul, map_mul, map_inv]
  have hclass : π xL = π gl := by
    calc
      π xL = φ (π lL) := hφl.symm
      _ = gbar * π lL * gbar⁻¹ := by rw [hgbar, MulAut.conj_apply]
      _ = π gL * π lL * (π gL)⁻¹ := by rw [hgL]
      _ = π gl := hπgl.symm
  have hclass' : (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥L) xL : oTwoQuot ↥L) =
      QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥L) gl := by
    simpa only [π, QuotientGroup.mk'_apply] using hclass
  have hdiv : xL / gl ∈ CFSG.Open.pCore 2 ↥L :=
    QuotientGroup.eq_iff_div_mem.mp hclass'
  have hmemp : ((xL / gl : ↥L) : G) ∈ pCoreOf 2 L :=
    Subgroup.mem_map_of_mem L.subtype hdiv
  simpa [xL, gl, Subgroup.coe_div, div_eq_mul_inv] using hmemp

end CFSG.GroupTheory.AlternatingFive
