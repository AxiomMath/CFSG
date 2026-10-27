module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.TwoActions
public import CFSG.Quasithin.Vol2.KGFactJ4M3Three
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.NaturalThree

public section

namespace CFSG.SectionRank.QTK.Insp443.J4

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.J4M3 CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam
  CFSG.Quasithin.KGC31 CFSG.Sporadic.J4 CFSG.QuasithinUnique.Vol2Native.A312L.Seven
  CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13.Ch4
  CFSG.Quasithin.H13.Ch4.E443
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

theorem card_range_le_of_ker_le {B X Y : Type*} [Group B] [Finite B] [Group X] [Group Y]
    (φ : B →* X) (θ : B →* Y) (h : φ.ker ≤ θ.ker) : Nat.card θ.range ≤ Nat.card φ.range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv] at h2
  have hk : Nat.card φ.ker ≤ Nat.card θ.ker := Subgroup.card_le_of_le h
  have hpos : 0 < Nat.card θ.ker := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have := Nat.mul_lt_mul_of_lt_of_le hlt hk hpos
  omega

section M3


noncomputable abbrev θ₂ : ↥M3 →* ↥(StatedSL 3 (ZMod 2)) := E16.eNHom hv0 M3_le_eNorm

theorem mem_Q_of_mem_KL_of_mem_centralizer {g : J} (h1 : g ∈ KL)
    (h2 : g ∈ Subgroup.centralizer (V0 : Set J)) : g ∈ Qg := by
  have h : g ∈ KL ⊓ Subgroup.centralizer (V0 : Set J) := ⟨h1, h2⟩
  rwa [KL_inf_centralizer_eq_K3, K3_eq_Q] at h

theorem isPGroup_Qg : IsPGroup 2 ↥Qg := IsPGroup.of_card (n := 15) card_Q

theorem M3_le_normalizer_Q : M3 ≤ Subgroup.normalizer (Qg : Set J) :=
  pCoreOf_M3_eq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M3

theorem Q_le_and_eq_V0 {L V : Subgroup J} (hLM : L ≤ M3)
    (hML : M3 ≤ Subgroup.normalizer (L : Set J)) (hper : ⁅L, L⁆ = L)
    (hVO : V ≤ pCoreOf 2 L) (hOC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set J))
    (hLV : L ≤ Subgroup.normalizer (V : Set J)) (hVc : V = ⁅V, L⁆) (hVne : V ≠ ⊥) :
    Qg ≤ L ∧ V = V0 ∧ (θ₂.comp (Subgroup.inclusion hLM)).range = ⊤ := by
  have : Group.IsPerfect ↥L := ⟨commutator_eq_top_of_perfect hper⟩
  set θ₁L : ↥L →* Equiv.Perm (Fin 5) := (rho3 j4Facts).comp (Subgroup.inclusion hLM) with hθ₁L
  set θ₂L : ↥L →* ↥(StatedSL 3 (ZMod 2)) := θ₂.comp (Subgroup.inclusion hLM) with hθ₂L
  have hθ₁mem : ∀ l : ↥L, θ₁L l = 1 ↔ (l : J) ∈ KL := fun l => rho3_eq_one_iff _
  have hθ₂mem : ∀ l : ↥L, θ₂L l = 1 ↔ (l : J) ∈ Subgroup.centralizer (V0 : Set J) :=
    fun l => eM3_eq_one_iff _
  have hsl : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hcsl : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 := E8.card_statedSL3
  have hQV : Qg ≤ L → V ≤ V0 := by
    intro hQL
    have hQO : Qg ≤ pCoreOf 2 L :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQL (hLM.trans M3_le_normalizer_Q)
        isPGroup_Qg
    have hVC : V ≤ Subgroup.centralizer (Qg : Set J) := by
      rw [Subgroup.le_centralizer_iff]
      exact hQO.trans hOC
    rw [← pCoreOf_M3_eq] at hVC
    exact hVC.trans centralizer_pCoreOf_M3_le
  rcases eq_bot_or_top_of_isPerfect (fun H hH => solvable_of_ne_top_card168 hcsl hH)
      (Group.IsPerfect.range θ₂L) with hb | ht
  ·
    exfalso
    have hLC : ∀ l ∈ L, l ∈ Subgroup.centralizer (V0 : Set J) := fun l hl =>
      (hθ₂mem ⟨l, hl⟩).mp (by
        have : θ₂L ⟨l, hl⟩ ∈ θ₂L.range := ⟨_, rfl⟩
        rwa [hb, Subgroup.mem_bot] at this)
    rcases isPerfect_perm_five (Group.IsPerfect.range θ₁L) with hb1 | ht1
    ·
      have hLQ : L ≤ Qg := fun l hl => mem_Q_of_mem_KL_of_mem_centralizer
        ((hθ₁mem ⟨l, hl⟩).mp (by
          have : θ₁L ⟨l, hl⟩ ∈ θ₁L.range := ⟨_, rfl⟩
          rwa [hb1, Subgroup.mem_bot] at this)) (hLC l hl)
      have hL1 : L = ⊥ := eq_bot_of_perfect_of_isPGroup hper (isPGroup_Qg.to_le hLQ)
      apply hVne
      rw [hVc, hL1, Subgroup.commutator_bot_right]
    ·
      have hyM : y3J ∈ M3 := Subgroup.centralizer_le_normalizer _ y3J_mem_centralizer
      obtain ⟨ym, hym⟩ : ∃ ym : ↥M3, (ym : J) = y3J := ⟨⟨y3J, hyM⟩, rfl⟩
      have hy3 : rho3 j4Facts ym ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        have h3 : (Equiv.Perm.sign (rho3 j4Facts ym)) ^ 3 = 1 := by
          rw [← map_pow, ← map_pow]
          have : ym ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hym]; exact y3J_pow_three)
          rw [this, map_one, map_one]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (rho3 j4Facts ym)) with h | h
        · exact h
        · rw [h] at h3
          exact absurd h3 (by decide)
      rw [← ht1] at hy3
      obtain ⟨l, hl⟩ := hy3
      have hlKL : (l : J)⁻¹ * y3J ∈ KL := by
        have : (rho3 j4Facts) ((Subgroup.inclusion hLM l)⁻¹ * ym) = 1 := by
          rw [map_mul, map_inv]
          change (θ₁L l)⁻¹ * _ = 1
          rw [hl, inv_mul_cancel]
        have h1 := (rho3_eq_one_iff ((Subgroup.inclusion hLM l)⁻¹ * ym)).mp this
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hym] at h1
      have hlC : (l : J)⁻¹ * y3J ∈ Subgroup.centralizer (V0 : Set J) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLC l l.2)) y3J_mem_centralizer
      have hQL : Qg ≤ L := Q_le_of_normal_y3 hLM hML l.2
        (mem_Q_of_mem_KL_of_mem_centralizer hlKL hlC)
      have hVV0 := hQV hQL
      apply hVne
      rw [hVc, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro l' hl'
      exact (Subgroup.mem_centralizer_iff.mp (hLC l' hl') v (hVV0 hv)).symm
  ·
    set N : Subgroup J := L ⊓ KL with hN
    have hNM : N ≤ M3 := inf_le_left.trans hLM
    have hMN : M3 ≤ Subgroup.normalizer (N : Set J) := fun m hm =>
      Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ⟨(Subgroup.mem_normalizer_iff.mp
        (hML hm) g).mp hg.1, (Subgroup.mem_normalizer_iff.mp (M3_le_normalizer_KL hm) g).mp hg.2⟩,
        fun hg => ⟨(Subgroup.mem_normalizer_iff.mp (hML hm) g).mpr hg.1,
          (Subgroup.mem_normalizer_iff.mp (M3_le_normalizer_KL hm) g).mpr hg.2⟩⟩
    have hNn : (N.subgroupOf M3).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
    have hθN : ((N.subgroupOf M3).map θ₂).Normal := hNn.map θ₂ eM3_surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf M3).map θ₂) with hb | ht'
    ·
      exfalso
      have hle : θ₁L.ker ≤ θ₂L.ker := by
        intro l hl
        have hlKL : (l : J) ∈ KL := (hθ₁mem l).mp hl
        have hlN : (⟨l, hLM l.2⟩ : ↥M3) ∈ N.subgroupOf M3 := Subgroup.mem_subgroupOf.mpr ⟨l.2, hlKL⟩
        have : θ₂ ⟨l, hLM l.2⟩ ∈ (N.subgroupOf M3).map θ₂ := Subgroup.mem_map_of_mem _ hlN
        rw [hb, Subgroup.mem_bot] at this
        exact this
      have h1 := card_range_le_of_ker_le θ₁L θ₂L hle
      rw [ht, Subgroup.card_top, hcsl] at h1
      have h2 : Nat.card θ₁L.range ≤ 120 := by
        have := Subgroup.card_le_card_group θ₁L.range
        rwa [Nat.card_perm, Nat.card_fin] at this
      omega
    ·
      have hxM : xM ∈ M3 := KL_le_M3 xM_mem_KL
      obtain ⟨xm, hxm⟩ : ∃ xm : ↥M3, (xm : J) = xM := ⟨⟨xM, hxM⟩, rfl⟩
      obtain ⟨l, hl, hlx⟩ : θ₂ xm ∈ (N.subgroupOf M3).map θ₂ := by rw [ht']; trivial
      have hlN := Subgroup.mem_subgroupOf.mp hl
      have hlKL : (l : J)⁻¹ * xM ∈ KL := KL.mul_mem (KL.inv_mem hlN.2) xM_mem_KL
      have hlC : (l : J)⁻¹ * xM ∈ Subgroup.centralizer (V0 : Set J) := by
        have h0 : E16.eNHom hv0 M3_le_eNorm (l⁻¹ * xm) = 1 := by
          rw [map_mul, map_inv]
          exact inv_mul_eq_one.mpr hlx
        have h1 := (eM3_eq_one_iff (l⁻¹ * xm)).mp h0
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, hxm] at h1
      have hQL : Qg ≤ L := Q_le_of_normal hLM hML hlN.1
        (mem_Q_of_mem_KL_of_mem_centralizer hlKL hlC)
      have hVV0 := hQV hQL
      refine ⟨hQL, ?_, ht⟩
      have hcV0 : Nat.card ↥V0 = 2 ^ 3 := by rw [← eSub_v0, card_eSub]
      have hdvd : Nat.card V ∣ 2 ^ 3 := hcV0 ▸ Subgroup.card_dvd_of_le hVV0
      obtain ⟨i, hi, hVi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have h4 : ¬ Nat.card V ≤ 4 := fun h4 => by
        apply hVne
        rw [hVc]
        exact comm_eq_bot_of_card_le_four hper hLV h4
      have h8 : Nat.card V = 2 ^ 3 := by
        rw [hVi] at h4 ⊢
        interval_cases i <;> simp at h4 ⊢
      exact Subgroup.eq_of_le_of_card_ge hVV0 (le_of_eq (by rw [h8, hcV0]))

theorem pCoreOf_eq_Q {L : Subgroup J} (hLM : L ≤ M3)
    (hML : M3 ≤ Subgroup.normalizer (L : Set J)) (hQL : Qg ≤ L) : pCoreOf 2 L = Qg := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQL
    (hLM.trans M3_le_normalizer_Q) isPGroup_Qg)
  rw [← pCoreOf_M3_eq]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)
    (hML.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem eq_KL_of_cardEq {L V : Subgroup J} (hLM : L ≤ M3)
    (hML : M3 ≤ Subgroup.normalizer (L : Set J)) (hper : ⁅L, L⁆ = L)
    (hVO : V ≤ pCoreOf 2 L) (hOC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set J))
    (hLV : L ≤ Subgroup.normalizer (V : Set J)) (hVc : V = ⁅V, L⁆) (hVne : V ≠ ⊥)
    (hcard : ∀ X Y : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), X.Normal → Y.Normal →
      CFSG.IsQuasisimple ↥X → CFSG.IsQuasisimple ↥Y → Nat.card X = Nat.card Y) : L = KL := by
  obtain ⟨hQL, -, hθ2⟩ := Q_le_and_eq_V0 hLM hML hper hVO hOC hLV hVc hVne
  have : Group.IsPerfect ↥L := ⟨commutator_eq_top_of_perfect hper⟩
  set θ₁L : ↥L →* Equiv.Perm (Fin 5) := (rho3 j4Facts).comp (Subgroup.inclusion hLM) with hθ₁L
  set θ₂L : ↥L →* ↥(StatedSL 3 (ZMod 2)) := θ₂.comp (Subgroup.inclusion hLM) with hθ₂L
  have hθ₁mem : ∀ l : ↥L, θ₁L l = 1 ↔ (l : J) ∈ KL := fun l => rho3_eq_one_iff _
  have hθ₂mem : ∀ l : ↥L, θ₂L l = 1 ↔ (l : J) ∈ Subgroup.centralizer (V0 : Set J) :=
    fun l => eM3_eq_one_iff _
  rcases isPerfect_perm_five (Group.IsPerfect.range θ₁L) with hb1 | ht1
  ·
    have hLK : L ≤ KL := fun l hl => (hθ₁mem ⟨l, hl⟩).mp (by
      have : θ₁L ⟨l, hl⟩ ∈ θ₁L.range := ⟨_, rfl⟩
      rwa [hb1, Subgroup.mem_bot] at this)
    refine le_antisymm hLK fun k hk => ?_
    obtain ⟨km, hkm⟩ : ∃ km : ↥M3, (km : J) = k := ⟨⟨k, KL_le_M3 hk⟩, rfl⟩
    obtain ⟨l, hl⟩ : θ₂ km ∈ θ₂L.range := by rw [hθ2]; trivial
    have h0 : E16.eNHom hv0 M3_le_eNorm ((Subgroup.inclusion hLM l)⁻¹ * km) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.mpr hl
    have hC := (eM3_eq_one_iff ((Subgroup.inclusion hLM l)⁻¹ * km)).mp h0
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hkm] at hC
    have hQ : (l : J)⁻¹ * k ∈ Qg :=
      mem_Q_of_mem_KL_of_mem_centralizer (KL.mul_mem (KL.inv_mem (hLK l.2)) hk) hC
    have e : k = (l : J) * ((l : J)⁻¹ * k) := by group
    rw [e]
    exact L.mul_mem l.2 (hQL hQ)
  ·
    exfalso
    have hsl : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
    have hθ₂s : Function.Surjective θ₂L := MonoidHom.range_eq_top.mp hθ2
    have hker : θ₁L.ker ⊓ θ₂L.ker = CFSG.pCore 2 ↥L := by
      rw [← Hex.pCoreOf_subgroupOf', pCoreOf_eq_Q hLM hML hQL]
      ext l
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      refine ⟨fun ⟨h1, h2⟩ => mem_Q_of_mem_KL_of_mem_centralizer ((hθ₁mem l).mp h1)
        ((hθ₂mem l).mp h2), fun h => ⟨(hθ₁mem l).mpr (Q_le_KL h), (hθ₂mem l).mpr ?_⟩⟩
      exact (KL_inf_centralizer_eq_K3 ▸ (K3_eq_Q ▸ h : (l : J) ∈ K3) :
        (l : J) ∈ KL ⊓ Subgroup.centralizer (V0 : Set J)).2
    exact false_of_two_actions E8.card_statedSL3 θ₁L ht1 θ₂L hθ₂s hker hcard

theorem ker_eNHom_KL :
    (E16.eNHom hv0 KL_le_eNorm).ker = Qg.subgroupOf KL := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E16.eNHom_eq_one_iff, eSub_v0, ← K3_eq_Q,
    ← KL_inf_centralizer_eq_K3]
  exact ⟨fun h => Subgroup.mem_inf.mpr ⟨x.2, h⟩, fun h => (Subgroup.mem_inf.mp h).2⟩

theorem conclK_KL' (MK : Subgroup J) : ConclK J KL (eSub hv0) MK := by
  have hO : pCoreOf 2 KL = Qg := pCoreOf_eq_Q KL_le_M3 M3_le_normalizer_KL Q_le_KL
  have hpk : CFSG.pCore 2 ↥KL = (E16.eNHom hv0 KL_le_eNorm).ker := by
    rw [← Hex.pCoreOf_subgroupOf', hO, ker_eNHom_KL]
  exact conclK_of_natural3 hv0 KL_le_eNorm surjective_eNHom_KL hpk MK

theorem conclK_KL (MK : Subgroup J) : ConclK J KL V0 MK := eSub_v0 ▸ conclK_KL' MK

theorem conclK_of_le_M3 {L V MK : Subgroup J} (hK : KConf J L V MK) (hLM : L ≤ M3)
    (hML : M3 ≤ Subgroup.normalizer (L : Set J)) : ConclK J L V MK := by
  have hV := (Q_le_and_eq_V0 hLM hML hK.perfect hK.le_pCoreOf hK.pCoreOf_le hK.le_normalizer
    hK.eq_commutator hK.ne_bot).2.1
  have hL := eq_KL_of_cardEq hLM hML hK.perfect hK.le_pCoreOf hK.pCoreOf_le hK.le_normalizer
    hK.eq_commutator hK.ne_bot hK.card_eq
  subst hV hL
  exact conclK_KL MK

end M3

end CFSG.SectionRank.QTK.Insp443.J4
