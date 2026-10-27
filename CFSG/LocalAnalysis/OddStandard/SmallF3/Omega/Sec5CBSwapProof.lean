module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSwapFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5cb_not_two_invs [Finite G] {P : Subgroup G} (hP : IsCyclic ↥P) {a b : G}
    (ha : a ∈ P) (hb : b ∈ P) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1)
    (hb2 : b * b = 1) : False := by
  classical
  haveI : Fintype ↥P := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥P) (n := 2) (by norm_num)
  refine absurd hle (not_le.mpr (Finset.two_lt_card_iff.mpr
    ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩))
  · simp
  · simpa [pow_two, Subtype.ext_iff] using ha2
  · simpa [pow_two, Subtype.ext_iff] using hb2
  · exact fun h => ha1 (congrArg Subtype.val h).symm
  · exact fun h => hb1 (congrArg Subtype.val h).symm
  · exact fun h => hab (congrArg Subtype.val h)

theorem sec5cb_not_mem_centralizer [Finite G] (h52a : Asc82Lemma52a) {r t : G}
    {L' : Subgroup G} (hS : Sec5Setting G r L') (hr2 : orderOf r = 2) (ht2 : orderOf t = 2)
    (hrt : r * t = t * r) (hne : r ≠ t) (hrc : r ∈ centralizer (L' : Set G)) :
    t ∉ centralizer (L' : Set G) := by
  intro htc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := centralizer (L' : Set G)
  have hQH : zpowers t ⊔ zpowers r ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr htc) (Subgroup.zpowers_le.mpr hrc)
  have htr : t ∈ centralizer ((zpowers r : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute r t from hrt).zpow_left k).eq
  have hQ2 : IsPGroup 2 (zpowers t ⊔ zpowers r : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_right' ?_ ?_ ?_
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2]; rfl)
    · exact (Subgroup.zpowers_le.mpr htr).trans (Subgroup.centralizer_le_normalizer _)
  have hsub : IsPGroup 2 ((zpowers t ⊔ zpowers r).subgroupOf H) :=
    IsPGroup.comap_subtype hQ2 (K := H)
  obtain ⟨P, hQP⟩ := hsub.exists_le_sylow
  have h52a' : ∀ P : Sylow 2 ↥H, IsCyclic (P : Subgroup ↥H) := h52a G r L' hS
  have hSyl : IsSylow2Of ((P : Subgroup ↥H).map H.subtype) H := isSylow2Of_map_sylow P
  haveI : IsCyclic ↥((P : Subgroup ↥H).map H.subtype) := sec5_isCyclic_of_isSylow2Of h52a' hSyl
  have hmem : ∀ x ∈ zpowers t ⊔ zpowers r, x ∈ (P : Subgroup ↥H).map H.subtype := fun x hx =>
    Subgroup.mem_map.mpr ⟨⟨x, hQH hx⟩, hQP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
    rw [← pow_two, ← hx]
    exact pow_orderOf_eq_one x
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h1 => by
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  exact sec5cb_not_two_invs this (hmem t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)))
    (hmem r (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))) (hne1 t ht2) (hne1 r hr2)
    (Ne.symm hne) (hsq t ht2) (hsq r hr2)

theorem sec5cb_orderOf_dvd_of_le {L' K : Subgroup G} (hKL : K ≤ L') (k : ↥K) :
    orderOf (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) ∣
      orderOf (QuotientGroup.mk (⟨(k : G), hKL k.2⟩ : ↥L') : ↥L' ⧸ Subgroup.center ↥L') := by
  set m := orderOf (QuotientGroup.mk (⟨(k : G), hKL k.2⟩ : ↥L') : ↥L' ⧸ Subgroup.center ↥L')
  have h1 : (QuotientGroup.mk (⟨(k : G), hKL k.2⟩ : ↥L') : ↥L' ⧸ Subgroup.center ↥L') ^ m = 1 :=
    pow_orderOf_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro y
  have hy := Subgroup.mem_center_iff.mp h1 ⟨(y : G), hKL y.2⟩
  have hy' : (y : G) * (k : G) ^ m = (k : G) ^ m * (y : G) :=
    congrArg (fun x : ↥L' => (x : G)) hy
  exact Subtype.ext hy'

theorem sec5cb_conj_comm {t : G} {L : Subgroup G} (g : G) (ht : ∀ y ∈ L, t * y = y * t) :
    ∀ y ∈ CFSG.conjugate L g, g⁻¹ * t * g * y = y * (g⁻¹ * t * g) := by
  intro y hy
  have hc := ht _ ((mem_conjugate_iff L g y).mp hy)
  calc g⁻¹ * t * g * y = g⁻¹ * (t * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * t) * g := by rw [hc]
    _ = y * (g⁻¹ * t * g) := by group

theorem asc82Fact58Swap_of (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a) (hO : Asc82Outside)
    (fkq : Asc82FactI1Layer) (fx : Asc82FactI1Cent) : Asc82Fact58Swap := by
  intro G _ _ t L S z r B A h
  obtain ⟨g, hg⟩ := h.conj_r
  refine ⟨g, hg, ?_⟩
  subst hg
  have hOm : IsOm6Z2 L := h.toSec5Ctx.toSec5Setting.isOm6Z2
  have ht2 : orderOf t = 2 := h.involution
  have hr2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact ht2
  have htB : t ∈ B := h.B_split.1
  have htL : t ∈ L := (Subgroup.mem_inf.mp (h.B_le htB)).1
  have hrt : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (h.B_le htB)).2
  have hLt : ∀ y ∈ L, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (h.component.1 hy)).symm
  have hrL : g⁻¹ * t * g ∉ L := by
    obtain ⟨α₀, V, _, _, _, Q, hQ, e, x, hdim, -, hx, hxt⟩ := h.type_r
    exact sec5c_r_not_mem hdim hx hxt
  have hne : g⁻¹ * t * g ≠ t := fun h' => hrL (by rw [h']; exact htL)
  have hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hrt.symm
  obtain ⟨hKq, k₀, hk₀⟩ := fkq G L hOm (g⁻¹ * t * g) hr2 h.type_r
  have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic ↥P :=
    fun P hP => sec5_isCyclic_of_isSylow2Of (h52a G t L h.toSec5Ctx.toSec5Setting) hP
  have hKLg : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g :=
    (le_twoPrimeRes_of_isQuasisimple hKq).trans (hO.thm2L G t L h.toSec5Ctx.toSec3SettingLB hcyc
      (asc82OddInnerOm6_holds G L (Or.inl hOm)) (-1) g hsC hne _ (Or.inl rfl))
  have hKL : layerCent L (g⁻¹ * t * g) ≤ L :=
    (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({g⁻¹ * t * g} : Set G)))).trans
      inf_le_left
  have hsI : Sec5Setting G (g⁻¹ * t * g) (CFSG.conjugate L g) :=
    h.toSec5Ctx.toSec5Setting.conjugate g
  have htCs : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hrt
  have htN : t ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    sec4_mem_normalizer h36 hsI.toSec3SettingLB t htCs
  have hrc : g⁻¹ * t * g ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (sec5cb_conj_comm g hLt y hy).symm
  have htnc : t ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    sec5cb_not_mem_centralizer h52a hsI hr2 ht2 hrt.symm hne hrc
  have h9 : 9 ∣ orderOf (QuotientGroup.mk (⟨(k₀ : G), hKLg k₀.2⟩ : ↥(CFSG.conjugate L g)) :
      ↥(CFSG.conjugate L g) ⧸ Subgroup.center ↥(CFSG.conjugate L g)) := by
    have h := sec5cb_orderOf_dvd_of_le hKLg k₀
    rwa [hk₀] at h
  exact fx G (CFSG.conjugate L g) (isOm6Z2_conjugate hOm g) t ht2 htN htnc
    ⟨(k₀ : G), hKLg k₀.2⟩ (hLt _ (hKL k₀.2)).symm h9

end CFSG.OddStandard.SmallF3.Omega
