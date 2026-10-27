module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.Assembly.E6FourNeighbourBar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped IsMulCommutative

theorem comp_quot {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S B D K : Subgroup Ω} {x : Ω} (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hB : IsElemAbelian p B) (hBx : B = Subgroup.zpowers x ⊔ B ⊓ S) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxC : x ∈ Subgroup.centralizer (S : Set Ω)) (hstd : GLAStdSubPre p B x S D K) :
    ∃ y : ↥S, (y : Ω) ∈ B ∧ (QuotientGroup.mk y : ↥S ⧸ Subgroup.center ↥S) ≠ 1 ∧
      CFSG.Open.IsComponentOf (modCentreImage S K) (Subgroup.centralizer
        ({(QuotientGroup.mk y : ↥S ⧸ Subgroup.center ↥S)} : Set (↥S ⧸ Subgroup.center ↥S))) := by
  classical
  unfold GLAStdSubPre at hstd
  rcases hstd with ⟨hDB, hDel, hDcard, hxD, _hKlayer, hKcomp, _hDcent⟩
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hxorder_dvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have hxorder_ne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hxorder : orderOf x = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf x) hxorder_dvd with h | h
    · exact absurd h hxorder_ne1
    · exact h
  have hxle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.mpr hxB
  have hBsup : (Subgroup.zpowers x).subgroupOf B ⊔ (B ⊓ S).subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hxle inf_le_left, ← hBx, Subgroup.subgroupOf_self]
  have hD_eq : D = Subgroup.zpowers x ⊔ D ⊓ S := by
    haveI : IsMulCommutative ↥B := hB.1
    refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hxD) inf_le_left)
    intro d hd
    have hdB : d ∈ B := hDB hd
    have hmem : (⟨d, hdB⟩ : ↥B) ∈
        (Subgroup.zpowers x).subgroupOf B ⊔ (B ⊓ S).subgroupOf B := by
      rw [hBsup]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.mp hmem
    have haz : (a : Ω) ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.mp ha
    have hcz : (c : Ω) ∈ B ⊓ S := Subgroup.mem_subgroupOf.mp hc
    have hval : (a : Ω) * (c : Ω) = d := congrArg Subtype.val hac
    have hc_eq : (c : Ω) = (a : Ω)⁻¹ * d := by
      rw [← hval]
      group
    have hcD : (c : Ω) ∈ D := by
      rw [hc_eq]
      exact D.mul_mem (D.inv_mem (Subgroup.zpowers_le.mpr hxD haz)) hd
    have hdmem : d ∈ Subgroup.zpowers x ⊔ D ⊓ S := by
      rw [← hval]
      exact Subgroup.mul_mem_sup haz (Subgroup.mem_inf.mpr ⟨hcD, (Subgroup.mem_inf.mp hcz).2⟩)
    exact hdmem
  have hnotle : ¬ D ⊓ S ≤ Subgroup.zpowers x := by
    intro hle
    have hDsub : D ≤ Subgroup.zpowers x := by
      rw [hD_eq]
      exact sup_le le_rfl hle
    have hle_card : Nat.card D ≤ p := by
      calc Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDsub
        _ = orderOf x := Nat.card_zpowers x
        _ = p := hxorder
    rw [hDcard] at hle_card
    nlinarith [hp.two_le]
  have hnotle_set : ¬ ((D ⊓ S : Subgroup Ω) : Set Ω) ⊆ (Subgroup.zpowers x : Set Ω) :=
    fun h => hnotle h
  obtain ⟨s, hsDS, hsx⟩ := Set.not_subset.mp hnotle_set
  have hsD : s ∈ D := (Subgroup.mem_inf.mp hsDS).1
  have hsS : s ∈ S := (Subgroup.mem_inf.mp hsDS).2
  have hsp : s ^ p = 1 := hDel.2 s hsD
  have hs1 : s ≠ 1 := fun h => hsx (h ▸ Subgroup.one_mem (Subgroup.zpowers x))
  have hsdvd : orderOf s ∣ p := orderOf_dvd_of_pow_eq_one hsp
  have hsne1 : orderOf s ≠ 1 := fun h => hs1 (orderOf_eq_one_iff.mp h)
  have hs_order : orderOf s = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf s) hsdvd with h | h
    · exact absurd h hsne1
    · exact h
  have hDsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers s := by
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers s ≤ D :=
      sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hsD)
    have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers s := by
      rw [lt_iff_le_and_ne]
      refine ⟨le_sup_left, ?_⟩
      intro heq
      exact hsx (heq.symm ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    have hcard_lt : Nat.card (Subgroup.zpowers x) <
        Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup Ω) :=
      Subgroup.card_lt_of_lt hlt
    have hgt : p < Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup Ω) := by
      rw [Nat.card_zpowers, hxorder] at hcard_lt
      exact hcard_lt
    have hdvd : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup Ω) ∣ p ^ 2 := by
      rw [← hDcard]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk_eq : k = 2 := by
      have hp2 : 2 ≤ p := hp.two_le
      interval_cases k
      · rw [hk] at hgt; simp only [pow_zero] at hgt; omega
      · rw [hk] at hgt; simp only [pow_one] at hgt; omega
      · rfl
    have hcard_sup : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup Ω) = p ^ 2 := by
      rw [hk, hk_eq]
    have hcard_le : Nat.card D ≤
        Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup Ω) := by
      rw [hcard_sup, hDcard]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard_le).symm
  have hCs : S ⊓ Subgroup.centralizer (D : Set Ω) =
      S ⊓ Subgroup.centralizer ({s} : Set Ω) := by
    apply le_antisymm
    · intro g hg
      exact Subgroup.mem_inf.mpr ⟨hg.1,
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsD) hg.2⟩
    · intro g hg
      refine Subgroup.mem_inf.mpr ⟨hg.1, ?_⟩
      have hDle : D ≤ Subgroup.centralizer ({g} : Set Ω) := by
        rw [hDsup]
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact Subgroup.mem_centralizer_iff.mp hxC g hg.1
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact (Subgroup.mem_centralizer_iff.mp hg.2 s (Set.mem_singleton s)).symm
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      exact (Subgroup.mem_centralizer_iff.mp (hDle hh) g (Set.mem_singleton g)).symm
  have hKcomp_s : CFSG.Open.IsComponentOf K (S ⊓ Subgroup.centralizer ({s} : Set Ω)) := by
    rwa [hCs] at hKcomp
  have hKS : K ≤ S := hKcomp_s.1.trans inf_le_left
  let y : ↥S := ⟨s, hsS⟩
  have hy_order : orderOf y = p := by
    change orderOf (⟨s, hsS⟩ : ↥S) = p
    rw [Subgroup.orderOf_mk, hs_order]
  have hyB : (y : Ω) ∈ B := hDB hsD
  have hyQ : (QuotientGroup.mk y : ↥S ⧸ Subgroup.center ↥S) ≠ 1 := by
    intro h1
    have hycenter : y ∈ Subgroup.center ↥S := (QuotientGroup.eq_one_iff y).mp h1
    have hdvd : orderOf y ∣ Nat.card (Subgroup.center ↥S) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥S) hycenter
    rw [hy_order] at hdvd
    exact hZ hdvd
  have hcentralizer_subgroupOf :
      (Subgroup.centralizer ({s} : Set Ω)).subgroupOf S =
        Subgroup.centralizer ({y} : Set ↥S) := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      apply Subtype.ext
      simpa using hz s (Set.mem_singleton s)
    · intro z hz
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      have hyz := hz y (Set.mem_singleton y)
      simpa using congrArg Subtype.val hyz
  have hupper : (S ⊓ Subgroup.centralizer ({s} : Set Ω)).subgroupOf S =
      Subgroup.centralizer ({y} : Set ↥S) := by
    rw [inf_comm, Subgroup.inf_subgroupOf_right, hcentralizer_subgroupOf]
  have hK₁_le : K.subgroupOf S ≤ Subgroup.centralizer ({y} : Set ↥S) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    have hkK : (k : Ω) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hkC : (k : Ω) ∈ Subgroup.centralizer ({s} : Set Ω) :=
      (Subgroup.mem_inf.mp (hKcomp_s.1 hkK)).2
    simpa using Subgroup.mem_centralizer_iff.mp hkC s (Set.mem_singleton s)
  have hK₁_sub : CFSG.Open.IsSubnormal (K.subgroupOf S)
      (Subgroup.centralizer ({y} : Set ↥S)) := by
    have h := hKcomp_s.2.1.comap S.subtype
    change CFSG.Open.IsSubnormal (K.subgroupOf S)
      ((S ⊓ Subgroup.centralizer ({s} : Set Ω)).subgroupOf S) at h
    rwa [hupper] at h
  have hK₁_q : CFSG.Open.IsQuasisimple (K.subgroupOf S) :=
    (CFSG.Open.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKS)).mpr hKcomp_s.2.2
  have hK₁_open : CFSG.Open.IsComponentOf (K.subgroupOf S)
      (Subgroup.centralizer ({y} : Set ↥S)) :=
    ⟨hK₁_le, hK₁_sub, hK₁_q⟩
  have hK₁ : CFSG.Assembly.IsComponentOf (K.subgroupOf S)
      (Subgroup.centralizer ({y} : Set ↥S)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hK₁_open
  have hKO : ¬ K.subgroupOf S ≤ Subgroup.center ↥S := by
    intro hle
    haveI : Group.IsPerfect ↥(K.subgroupOf S) := ⟨hK₁_q.1⟩
    have hbot : K.subgroupOf S = ⊥ :=
      CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot (K.subgroupOf S) hle
    haveI : Nontrivial ↥(K.subgroupOf S) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hK₁_q
    exact (Subgroup.nontrivial_iff_ne_bot (K.subgroupOf S)).mp inferInstance hbot
  obtain ⟨-, hKbar_comp⟩ :=
    CFSG.Assembly.bar_isComponentOf (H := ↥S) (p := p) (Subgroup.center ↥S)
      hp hZ hy_order hK₁ hKO
  refine ⟨y, hyB, hyQ, ?_⟩
  have h := CFSG.Assembly.isComponentOf_iff_open.mp hKbar_comp
  simpa only [modCentreImage, QuotientGroup.mk'_apply] using h

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
