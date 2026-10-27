module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConfig
public import CFSG.Quasithin.Vol2.KGFactL52Mod10
public import CFSG.Quasithin.Vol2.Ch4Sec4L448
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411A
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.NaturalThree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31RuRefKBase

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}

theorem KConfig.eight_le_card (h : KConfig K L V MK) : 8 ≤ Nat.card V := by
  by_contra h8
  push Not at h8
  have hP : IsPGroup 2 V := h.elemAbelian.isPGroup
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hn2 : n ≤ 2 := by
    have h2n : 2 ^ n < 8 := by rwa [hn] at h8
    have h2n' : 2 ^ n < 2 ^ 3 := by simpa using h2n
    have hn3 : n < 3 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h2n'
    omega
  have hidx : ((⊥ : Subgroup K).subgroupOf V).index ≤ 4 := by
    rw [Subgroup.bot_subgroupOf V, Subgroup.index_bot, hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hn2
      _ = 4 := by norm_num
  have hbotN : ∀ H : Subgroup K, H ≤ Subgroup.normalizer ((⊥ : Subgroup K) : Set K) :=
    fun H _ _ => by
      rw [Subgroup.normalizer_eq_top (⊥ : Subgroup K)]
      exact Subgroup.mem_top _
  have hmem := CFSG.Quasithin.H13.Ch4.commutator_mem_of_perfect_of_index_le_four
    (L := L) (V := V) (W := ⊥) h.perfect h.le_normalizer (hbotN L) (hbotN V) hidx
  have hcommLV : ⁅L, V⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact Subgroup.commutator_le.mpr fun l hl v hv => by
      simpa [commutatorElement_def] using hmem l hl v hv
  have hcomm : ⁅V, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcommLV
  have hVbot : V = ⊥ := by rw [h.eq_commutator, hcomm]
  exact h.ne_bot hVbot

private theorem KConfig.conclK_of_eSub_of_commutator_le {G : Type} [Group G] [Finite G]
    {v : Fin 3 → G} (hv : EBasis v) {L MK : Subgroup G} (h : KConfig G L (eSub hv) MK)
    (hF : ⁅L ⊓ Subgroup.centralizer (eSub hv : Set G), L⁆ ≤ pCoreOf 2 L) :
    ConclK G L (eSub hv) MK := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ≤ eNorm hv := h.le_normalizer
  have hθ : ∀ l : ↥L, E16.eNHom hv hLN l = 1 ↔
      (l : G) ∈ Subgroup.centralizer (eSub hv : Set G) := fun l => E16.eNHom_eq_one_iff hv hLN l
  have : Group.IsPerfect ↥L :=
    ⟨CFSG.Quasithin.H13.Ch4.E443.F4411.commutator_eq_top_of_perfect h.perfect⟩
  haveI hsl : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hsurj : Function.Surjective (E16.eNHom hv hLN) := by
    rw [← MonoidHom.range_eq_top]
    rcases CFSG.Quasithin.J4Fam.eq_bot_or_top_of_isPerfect
        (fun H hH => CFSG.Quasithin.J4Fam.solvable_of_ne_top_card168 E8.card_statedSL3 hH)
        (Group.IsPerfect.range (E16.eNHom hv hLN)) with hb | ht
    · exfalso
      have hLC : L ≤ Subgroup.centralizer (eSub hv : Set G) := fun l hl =>
        (hθ ⟨l, hl⟩).mp (by
          have : E16.eNHom hv hLN ⟨l, hl⟩ ∈ (E16.eNHom hv hLN).range := ⟨_, rfl⟩
          rwa [hb, Subgroup.mem_bot] at this)
      have hcomm : ⁅eSub hv, L⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          ((Subgroup.le_centralizer_iff (H := L) (K := eSub hv)).mp hLC)
      apply h.ne_bot
      rw [h.eq_commutator, hcomm]
    · exact ht
  have hpk : CFSG.pCore 2 ↥L = (E16.eNHom hv hLN).ker := by
    have hpc_le_ker : CFSG.pCore 2 ↥L ≤ (E16.eNHom hv hLN).ker := by
      rw [← Hex.pCoreOf_subgroupOf' L]
      intro l hl
      rw [Subgroup.mem_subgroupOf] at hl
      rw [MonoidHom.mem_ker, hθ]
      exact h.pCoreOf_le hl
    let E := ↥L ⧸ CFSG.pCore 2 ↥L
    let π : ↥L →* E := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    let Z : Subgroup E := (E16.eNHom hv hLN).ker.map π
    haveI hZnormal : Z.Normal :=
      (MonoidHom.normal_ker (E16.eNHom hv hLN)).map π (QuotientGroup.mk'_surjective _)
    have hEperf : _root_.commutator E = ⊤ := by
      have h2 : (_root_.commutator ↥L).map π = _root_.commutator E := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      rw [← h2, Group.isPerfect_def.mp this, Subgroup.map_top_of_surjective π
        (QuotientGroup.mk'_surjective _)]
    have hZcenter : Z ≤ Subgroup.center E := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
      have hxK : (x : G) ∈ L ⊓ Subgroup.centralizer (eSub hv : Set G) :=
        ⟨x.2, (hθ x).mp hx⟩
      have hcommK : ⁅(x : G), (l : G)⁆ ∈ pCoreOf 2 L :=
        hF (Subgroup.commutator_mem_commutator hxK l.2)
      have hcommL : ⁅x, l⁆ ∈ CFSG.pCore 2 ↥L := by
        rw [← Hex.pCoreOf_subgroupOf' L, Subgroup.mem_subgroupOf]
        have hcoe : ((⁅x, l⁆ : ↥L) : G) = ⁅(x : G), (l : G)⁆ :=
          map_commutatorElement L.subtype x l
        rw [hcoe]
        exact hcommK
      have hcommL' : ⁅l, x⁆ ∈ CFSG.pCore 2 ↥L := by
        rw [← commutatorElement_inv x l]
        exact (CFSG.pCore 2 ↥L).inv_mem hcommL
      have hdecomp : l * x = ⁅l, x⁆ * (x * l) := by
        rw [commutatorElement_def]
        group
      calc π l * π x = π (l * x) := (map_mul π l x).symm
        _ = π (⁅l, x⁆ * (x * l)) := by rw [hdecomp]
        _ = π ⁅l, x⁆ * π (x * l) := map_mul π _ _
        _ = 1 * π (x * l) := by
              rw [show π ⁅l, x⁆ = 1 from
                (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) _).mpr hcommL']
        _ = π (x * l) := one_mul _
        _ = π x * π l := map_mul π x l
    have hZodd : Odd (Nat.card Z) := by
      by_contra hnotodd
      have h2dvd : 2 ∣ Nat.card Z :=
        even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnotodd)
      obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2dvd
      have hzEorder : orderOf (z : E) = 2 := (Subgroup.orderOf_coe z).trans hzorder
      have hzE2 : (z : E) ^ 2 = 1 := by
        have hz2 : z ^ 2 = 1 := by
          have h := pow_orderOf_eq_one z
          rwa [hzorder] at h
        simpa using congrArg (Subgroup.subtype Z) hz2
      let P : Subgroup E := Subgroup.zpowers (z : E)
      have hPnormal : P.Normal := by
        refine Subgroup.normal_of_le_center fun x hx => ?_
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact (Subgroup.center E).zpow_mem (hZcenter z.2) m
      let Q : Subgroup ↥L := P.comap π
      have hQnormal : Q.Normal := hPnormal.comap π
      have hQ2 : IsPGroup 2 Q := by
        refine IsPGroup.iff_orderOf.mpr fun q => ?_
        have hxP : π (q : ↥L) ∈ P := q.2
        have hx2 : (q : ↥L) ^ 2 ∈ CFSG.pCore 2 ↥L := by
          refine (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) _).mp ?_
          show π ((q : ↥L) ^ 2) = 1
          rw [map_pow]
          exact (isElemAbelian_zpowers (p := 2) hzE2).2 (π (q : ↥L)) hxP
        obtain ⟨m, hm⟩ :=
          (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCore_isPGroup 2))
            ⟨(q : ↥L) ^ 2, hx2⟩
        have hx2ord : orderOf ((q : ↥L) ^ 2) = 2 ^ m :=
          (Subgroup.orderOf_coe ⟨(q : ↥L) ^ 2, hx2⟩).trans hm
        have hxpow : (q : ↥L) ^ (2 ^ (m + 1)) = 1 := by
          rw [show 2 ^ (m + 1) = 2 * 2 ^ m by ring, pow_mul, ← hx2ord]
          exact pow_orderOf_eq_one _
        have hdvd : orderOf (q : ↥L) ∣ 2 ^ (m + 1) := orderOf_dvd_of_pow_eq_one hxpow
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        exact ⟨j, (Subgroup.orderOf_coe q).symm.trans hj⟩
      have hQle : Q ≤ CFSG.pCore 2 ↥L := by
        unfold CFSG.pCore
        exact le_sSup ⟨hQnormal, hQ2⟩
      have hPbot : P = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
        have hxQ : x ∈ Q := by
          rw [Subgroup.mem_comap]
          exact hy
        have hxker : x ∈ π.ker := by
          rw [QuotientGroup.ker_mk']
          exact hQle hxQ
        exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp hxker)
      have hzP : (z : E) ∈ P := Subgroup.mem_zpowers _
      have hz1 : (z : E) = 1 := Subgroup.mem_bot.mp (hPbot ▸ hzP)
      rw [hz1, orderOf_one] at hzEorder
      norm_num at hzEorder
    have hcardEZ : Nat.card (E ⧸ Z) = 168 := by
      let e : (E ⧸ Z) ≃* ↥(StatedSL 3 (ZMod 2)) :=
        (QuotientGroup.quotientQuotientEquivQuotient (N := CFSG.pCore 2 ↥L)
          (M := (E16.eNHom hv hLN).ker) hpc_le_ker).trans
          (QuotientGroup.quotientKerEquivOfSurjective (E16.eNHom hv hLN) hsurj)
      rw [Nat.card_congr e.toEquiv, E8.card_statedSL3]
    have hcyc : ∀ r : ℕ, r.Prime → r ∣ Nat.card Z →
        ∀ S : Sylow r (E ⧸ Z), IsCyclic S := by
      intro r hrprime hrZ S
      let : Fact r.Prime := ⟨hrprime⟩
      have hr2 : r ≠ 2 := by
        intro h2
        exact hZodd.not_two_dvd_nat (h2 ▸ hrZ)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
      have hdvd : r ^ n ∣ 168 := by
        have h1 := Subgroup.card_subgroup_dvd_card (S : Subgroup (E ⧸ Z))
        rw [hcardEZ] at h1
        rwa [hn] at h1
      have hn1 : n ≤ 1 := by
        by_contra hn2
        have hsq : r ^ 2 ∣ 168 := (pow_dvd_pow r (by omega)).trans hdvd
        have hle : r ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hsq
        have hr12 : r ≤ 12 := by nlinarith
        have hr2' := hrprime.two_le
        interval_cases r <;> first | exact hr2 rfl | norm_num at hsq
      have hdvdR : Nat.card (S : Subgroup (E ⧸ Z)) ∣ r := by
        rw [hn]
        interval_cases n <;> simp
      exact isCyclic_of_card_dvd_prime hdvdR
    have hZbot : Z = ⊥ :=
      eq_bot_of_le_center_of_isCyclic_sylow hEperf Z hZcenter hcyc
    have hker_le : (E16.eNHom hv hLN).ker ≤ CFSG.pCore 2 ↥L := by
      intro x hx
      have hxZ : π x ∈ Z := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hZbot] at hxZ
      have hxker : x ∈ π.ker := Subgroup.mem_bot.mp hxZ
      rwa [QuotientGroup.ker_mk'] at hxker
    exact le_antisymm hpc_le_ker hker_le
  exact conclK_of_natural3 hv hLN hsurj hpk MK

theorem KConfig.conclK_of_card_le_eight (h : KConfig K L V MK)
    (hF : ⁅L ⊓ Subgroup.centralizer (V : Set K), L⁆ ≤ pCoreOf 2 L)
    (hV : Nat.card V ≤ 8) : ConclK K L V MK := by
  have h8 := h.eight_le_card
  have hVeq : Nat.card V = 8 := le_antisymm hV h8
  letI : IsMulCommutative ↥V := h.elemAbelian.1
  have hE2 : CFSG.Quasithin.IsE2 3 ↥V :=
    CFSG.Quasithin.KGC31.Ru.isE2_of_card' (n := 3)
      (fun x y => mul_comm' x y)
      (fun x => by
        apply Subtype.ext
        have hx : (x : K) * (x : K) = 1 := by
          simpa [pow_two] using h.elemAbelian.2 x x.2
        simpa using hx)
      (by rw [hVeq]; norm_num)
  obtain ⟨v, hv, hveq⟩ := CFSG.Quasithin.H13.Ch4.exists_eBasis_of_isE2 hE2
  rw [← hveq] at h hF ⊢
  exact KConfig.conclK_of_eSub_of_commutator_le hv h hF

end CFSG.SectionRank.QTK.Insp443

end
