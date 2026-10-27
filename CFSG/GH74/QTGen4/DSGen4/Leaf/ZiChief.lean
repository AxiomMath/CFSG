module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem mem_dsCentMod_iff {G : Type} [Group G] {P L Q : Subgroup G} {p : G} :
    p ∈ dsCentMod P L Q ↔ p ∈ P ∧ p ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅p, l⁆ ∈ Q :=
  Iff.rfl

private theorem mem_of_odd_relIndex_of_isPGroup {G : Type} [Group G] [Finite G] {Q D : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (Q : Set G)) (hodd : Odd (Q.relIndex D)) {x : G} (hxD : x ∈ D)
    (hx : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ Q := by
  haveI : (Q.subgroupOf D).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hDN g.2) _).mp hn⟩
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyk : (⟨x, hxD⟩ : D) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
  have hq1 : (QuotientGroup.mk' (Q.subgroupOf D) (⟨x, hxD⟩ : D)) ^ 2 ^ k = 1 := by
    rw [← map_pow, hyk, map_one]
  have hq2 : (QuotientGroup.mk' (Q.subgroupOf D) (⟨x, hxD⟩ : D)) ^
      Nat.card (D ⧸ Q.subgroupOf D) = 1 :=
    pow_card_eq_one'
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (D ⧸ Q.subgroupOf D)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 := pow_gcd_eq_one.mpr ⟨hq1, hq2⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

private theorem mem_pCoreOf_of_normalizes {G : Type} [Group G] [Finite G] {L C : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hLC : ∀ g ∈ L, ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (hcore : pCoreOf 2 L ≤ C) (hnot : ¬ L ≤ C) {l : G} (hl : l ∈ L) (hlC : l ∈ C) :
    l ∈ pCoreOf 2 L := by
  haveI hsimp : IsSimpleGroup (oTwoQuot ↥L) := by
    obtain ⟨e⟩ := hq
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
        (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num)
    exact e.isSimpleGroup
  haveI hNn : (Subgroup.comap L.subtype C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap] at hn ⊢
    simpa using hLC g.1 g.2 n.1 (by simpa using hn)⟩
  have hpN : pCore 2 ↥L ≤ Subgroup.comap L.subtype C := fun x hx => by
    rw [Subgroup.mem_comap]
    exact hcore (Subgroup.mem_map_of_mem L.subtype hx)
  haveI : ((Subgroup.comap L.subtype C).map (QuotientGroup.mk' (pCore 2 ↥L))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal
      ((Subgroup.comap L.subtype C).map (QuotientGroup.mk' (pCore 2 ↥L))) with hbot | htop
  · have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥L))
      (show (⟨l, hl⟩ : ↥L) ∈ Subgroup.comap L.subtype C from hlC)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff _).mp h1)
  · exfalso
    apply hnot
    have hntop : Subgroup.comap L.subtype C = ⊤ := by
      have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 ↥L))) htop
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top,
        sup_eq_left.mpr hpN] at h
      exact h
    intro x hx
    have hxN : (⟨x, hx⟩ : ↥L) ∈ Subgroup.comap L.subtype C := by
      rw [hntop]
      exact Subgroup.mem_top _
    exact hxN

theorem leafZiChief [DSLeaf LeafZiStructure] [DSLeaf LeafFaithfulA5] [DSLeaf LeafFrattiniChief] [DSLeaf LeafM2] [DSLeaf LeafRankBounds] : LeafZiChief := by
  intro G _ _ L1 L2 S h hq hnc
  have hPN : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    F1.parabolic_le_normalizer h.hyp
  have hA5par : A5Par L1 (L1 ⊔ bigB L1 L2 S) :=
    ⟨le_sup_left, hPN, F1.parabolic_charTwo h.hyp, hq⟩
  obtain ⟨-, -, hZiOm, hOmEl, hOmCard, hZiN, -⟩ := zi_structure h
  obtain ⟨hOmComm, hOmSq⟩ := hOmEl
  have hOmC : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ centerOf (dsQ L1 L2 S) :=
    (Subgroup.closure_le _).2 fun x hx => hx.1
  have hOmQ : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ dsQ L1 L2 S := hOmC.trans inf_le_left
  have hZ1Q : dsZi L1 S ≤ dsQ L1 L2 S := hZiOm.trans hOmQ
  have hQP : dsQ L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hZ1P : dsZi L1 S ≤ L1 ⊔ bigB L1 L2 S := hZ1Q.trans hQP
  have hZ1cQ : ∀ e ∈ dsZi L1 S, ∀ q ∈ dsQ L1 L2 S, q * e = e * q := fun e he q hq' =>
    Subgroup.mem_centralizer_iff.mp (hOmC (hZiOm he)).2 q hq'
  have hZ1comm : ∀ x ∈ dsZi L1 S, ∀ y ∈ dsZi L1 S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hOmComm.is_comm.comm ⟨x, hZiOm hx⟩ ⟨y, hZiOm hy⟩)
  have hZ1sq : ∀ e ∈ dsZi L1 S, e ^ 2 = 1 := fun e he => hOmSq e (hZiOm he)
  have hZ1sec : IsElemSec ⊥ (dsZi L1 S) := by
    unfold IsElemSec
    refine ⟨bot_le, Subgroup.commutator_le.mpr fun a ha b hb => ?_,
      fun e he => Subgroup.mem_bot.mpr (hZ1sq e he)⟩
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hZ1comm a ha b hb))
  have hZ1card : Nat.card (dsZi L1 S) ≤ 16 :=
    (Subgroup.card_le_of_le hZiOm).trans hOmCard
  have hPK : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [(Subgroup.normalizer_eq_top_iff (H := (⊥ : Subgroup G))).mpr inferInstance]
    exact le_top
  have hcardZ1 : (⊥ : Subgroup G).relIndex (dsZi L1 S) ≤ 16 := by
    rw [Subgroup.relIndex_bot_left]
    exact hZ1card
  have hcore : ∀ q ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S), ∀ e ∈ dsZi L1 S, ⁅q, e⁆ ∈ (⊥ : Subgroup G) :=
    fun q hq' e he =>
      Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hZ1cQ e he q hq'))
  have hnt : ∃ l ∈ L1, ∃ e ∈ dsZi L1 S, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
    by_contra hcon
    push_neg at hcon
    apply hnc
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro e he l hl
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hcon l hl e he)
  have hfa : A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsZi L1 S) ⊥ :=
    faithful_a5 (P := L1 ⊔ bigB L1 L2 S) (L := L1) (E := dsZi L1 S) (K := ⊥) le_sup_left hPN hZ1P
      hZiN hPK hZ1sec hcardZ1 hq hcore hnt
  have hcardZ1' : Nat.card (dsZi L1 S) = 16 := by
    have h16 := hfa.card
    rwa [Subgroup.relIndex_bot_left] at h16
  have hconj2 : dsZi L1 S = dsOmega1 (centerOf (dsQ L1 L2 S)) :=
    Subgroup.eq_of_le_of_card_ge hZiOm (by rw [hcardZ1']; exact hOmCard)
  have hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := by
    have hsyl : IsSylowTwoOf S (bigB L1 L2 S) := F1.isSylowTwoOf_bigB_of_normal h.hyp h.bnorm
    have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
      (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (F1.pCoreOf_parabolic_le_bigB h.hyp) hBN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl)
  have hconj3 : dsZ S = dsZi L1 S ⊓ Subgroup.centralizer (S : Set G) := by
    refine le_antisymm (le_inf (dsZ_le_dsZi L1 S) ((dsZ_le_center S).trans inf_le_right)) ?_
    intro z hz
    obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzS : z ∈ S := hQS (hZ1Q hzZ)
    have hmem : z ∈ {x | x ∈ centerOf S ∧ x ^ 2 = 1} :=
      ⟨Subgroup.mem_inf.mpr ⟨hzS, hzC⟩, hZ1sq z hzZ⟩
    exact Subgroup.subset_closure hmem
  have hZ1N : ∀ g ∈ L1 ⊔ bigB L1 L2 S, ∀ e ∈ dsZi L1 S, g * e * g⁻¹ ∈ dsZi L1 S :=
    fun g hg e he => (Subgroup.mem_normalizer_iff.mp (hZiN hg) e).mp he
  have hCZ : ∀ g ∈ L1 ⊔ bigB L1 L2 S, ∀ c ∈ Subgroup.centralizer (dsZi L1 S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (dsZi L1 S : Set G) := by
    intro g hg c hc
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have he' : g⁻¹ * e * g⁻¹⁻¹ ∈ dsZi L1 S := hZ1N g⁻¹ ((L1 ⊔ bigB L1 L2 S).inv_mem hg) e he
    have key := Subgroup.mem_centralizer_iff.mp hc _ he'
    calc e * (g * c * g⁻¹) = (g * (g⁻¹ * e * g⁻¹⁻¹) * g⁻¹) * (g * c * g⁻¹) := by group
      _ = g * ((g⁻¹ * e * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * e * g⁻¹⁻¹)) * g⁻¹ := by rw [key]
      _ = g * c * g⁻¹ * e := by group
  have hkey : ∀ l ∈ L1, (∀ e ∈ dsZi L1 S, e * l = l * e) → l ∈ dsQ L1 L2 S := by
    intro l hl hlc
    have hcoreC : pCoreOf 2 L1 ≤ Subgroup.centralizer (dsZi L1 S : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun e he =>
        (hZ1cQ e he x (F1.pCoreOf_le_pCoreOf_parabolic h.hyp hx)).symm
    have hnot : ¬ L1 ≤ Subgroup.centralizer (dsZi L1 S : Set G) := by
      intro hle
      apply hnc
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro e he l' hl'
      exact Subgroup.mem_bot.mpr
        (commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp (hle hl') e he))
    exact F1.pCoreOf_le_pCoreOf_parabolic h.hyp
      (mem_pCoreOf_of_normalizes hq (fun g hg c hc => hCZ g (Subgroup.mem_sup_left hg) c hc) hcoreC hnot hl
        (Subgroup.mem_centralizer_iff.mpr hlc))
  have hconj4 : ∀ x ∈ L1 ⊔ bigB L1 L2 S, IsPGroup 2 (Subgroup.zpowers x) →
      (∀ e ∈ dsZi L1 S, ⁅x, e⁆ = 1) → x ∈ dsQ L1 L2 S := by
    intro x hx hx2 hxc
    have hxC : x ∈ Subgroup.centralizer (dsZi L1 S : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun e he =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hxc e he)).symm
    have hxD : x ∈ dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
      refine mem_dsCentMod_iff.mpr ⟨hx, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx,
        fun l hl => ?_⟩
      have hxl : ⁅x, l⁆ ∈ L1 := by
        rw [commutatorElement_def]
        exact L1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPN hx) l).mp hl) (L1.inv_mem hl)
      have hxlC : ⁅x, l⁆ ∈ Subgroup.centralizer (dsZi L1 S : Set G) := by
        rw [commutatorElement_def]
        have h2 := (Subgroup.centralizer (dsZi L1 S : Set G)).mul_mem hxC
          (hCZ l (Subgroup.mem_sup_left hl) x⁻¹ ((Subgroup.centralizer (dsZi L1 S : Set G)).inv_mem hxC))
        have e1 : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
        rw [e1]
        exact h2
      exact hkey _ hxl (Subgroup.mem_centralizer_iff.mp hxlC)
    obtain ⟨T, hT, hQT⟩ := F1.exists_isSylowTwoOf_ge
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (L1 ⊔ bigB L1 L2 S))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L1 ⊔ bigB L1 L2 S))
    have hodd := (m2 hA5par hT hQT).2.1
    have hDN : dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤
        Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
      fun d hd => (mem_dsCentMod_iff.mp hd).2.1
    exact mem_of_odd_relIndex_of_isPGroup hDN hodd hxD hx2
  exact ⟨hfa, hconj2, hconj3, hconj4⟩

end CFSG.GH74.QTGen4.DSGen4
