module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Star

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

theorem relIndex_sup_eq_card_of_coprime {G : Type*} [Group G] [Finite G] {O H : Subgroup G}
    [O.Normal] (hcop : Nat.Coprime (Nat.card O) (Nat.card H)) :
    H.relIndex (O ⊔ H) = Nat.card O := by
  have hOH : O ⊓ H = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have h1 := Subgroup.relIndex_mul_card H (O ⊔ H)
  have h2 := Subgroup.relIndex_mul_card O (O ⊔ H)
  have h3 := Subgroup.relIndex_mul_card O H
  rw [inf_of_le_left le_sup_right] at h1
  rw [inf_of_le_left le_sup_left] at h2
  rw [hOH, Subgroup.card_bot, mul_one] at h3
  rw [Subgroup.relIndex_sup_left, h3] at h2
  have hH : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hH (by rw [h1, ← h2, mul_comm])

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem Setting.not_centralizer_le_of_mem_normalizer (h : Setting J Q B) {w g : J}
    (hww : w * w = centralElt J) (hg : g ∈ quasiNormalizer w) (hgB : g ∉ B) :
    ¬ Subgroup.centralizer ({(w : J ⧸ Subgroup.center J)} : Set (J ⧸ Subgroup.center J)) ≤
      B.map (QuotientGroup.mk' (Subgroup.center J)) := fun hle =>
  hgB ((h.mk_mem_map_iff g).mp
    (hle (Subgroup.mem_centralizer_singleton_iff.mpr
      ((h.mem_normalizer_zpowers_iff_commute hww).mp hg).eq)))

theorem StarLift.exists_mem_quasiNormalizer_not_mem (hu : StarLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (T : Sylow 2 (quasiNormalizer u)) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L) {w : J}
    (hw : w ∈ partCRight T L) (hwB : w ∈ B) (hww : w * w = centralElt J) :
    ∃ g ∈ quasiNormalizer w, g ∉ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ⟨-, ht₀K⟩, rfl⟩ := hw
  obtain ⟨l', hlL, hlY⟩ := IsConcreteLE.not_le_iff_exists.mp hL.not_le
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 (quasiNormalizer u)) l'
  have hlB : (l : J) ∉ B := fun h' => hlY ((hu.mk_mem_quasiImage_iff h hz hu.rank l).mpr h')
  have hcomm : quasiMk u l * quasiMk u t₀ = quasiMk u t₀ * quasiMk u l :=
    Subgroup.mem_centralizer_iff.mp ht₀K _ hlL
  have hlt : l * t₀ * l⁻¹ * t₀⁻¹ ∈ CFSG.pPrimeCore 2 (quasiNormalizer u) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have hc' : ((l * t₀ : quasiNormalizer u) : QuasiQuotient u) = (t₀ * l : quasiNormalizer u) :=
      by simpa using hcomm
    rw [← QuotientGroup.mk_mul, hc', QuotientGroup.mk_mul]
    group
  set C := CFSG.pPrimeCore 2 (quasiNormalizer u) ⊔ Subgroup.zpowers t₀ with hCdef
  have hle : C ≤ C.comap (MulAut.conj l).toMonoidHom := by
    refine _root_.sup_le (fun o ho => Subgroup.mem_comap.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mem_sup_left
        ((inferInstance : (CFSG.pPrimeCore 2 (quasiNormalizer u)).Normal).conj_mem o ho l)
    · rw [Subgroup.mem_comap]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show l * t₀ * l⁻¹ = (l * t₀ * l⁻¹ * t₀⁻¹) * t₀ by group]
      exact C.mul_mem (Subgroup.mem_sup_left hlt)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))
  have hlC : ∀ c ∈ C, l * c * l⁻¹ ∈ C := fun c hc => by
    have := hle hc
    simpa using this
  have hord : orderOf t₀ = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact h.orderOf_eq_four hww
  have hH2 : IsPGroup 2 (Subgroup.zpowers t₀) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hodd := quasi_oddCore_odd u
  have hcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore 2 (quasiNormalizer u)))
      (Nat.card (Subgroup.zpowers t₀)) := by
    rw [Nat.card_zpowers, hord, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
  have hidx := relIndex_sup_eq_card_of_coprime hcop
  let P₀ : Sylow 2 C := (hH2.comap_subtype (K := C)).toSylow (by
    change ¬ 2 ∣ (Subgroup.zpowers t₀).relIndex C
    rw [hidx]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))
  have hP₀ : (P₀ : Subgroup C).map C.subtype = Subgroup.zpowers t₀ :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_right
  obtain ⟨c, hcC, hcl⟩ :=
    CFSG.ShultStronglyClosedTI.SuzukiExclusion.exists_mul_mem_normalizer_of_sylow
    (H := Subgroup.normalizer (C : Set (quasiNormalizer u)))
    (fun g hg c hc => (Subgroup.mem_normalizer_iff.mp hg c).mp hc) P₀ hP₀
    (mem_normalizer_of_conj_mem hlC)
  have hCB : C ≤ B.subgroupOf (quasiNormalizer u) :=
    _root_.sup_le (hu.oddCore_le h hz hu.rank)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hwB))
  have hcB : (c : J) ∈ B := Subgroup.mem_subgroupOf.mp (hCB hcC)
  refine ⟨((c * l : quasiNormalizer u) : J), mem_normalizer_of_conj_mem fun y hy => ?_,
    fun hg => hlB ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk : (c * l) * t₀ ^ k * (c * l)⁻¹ ∈ Subgroup.zpowers t₀ :=
      (Subgroup.mem_normalizer_iff.mp hcl (t₀ ^ k)).mp (Subgroup.zpow_mem_zpowers t₀ k)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa using this
  · have : (l : J) = (c : J)⁻¹ * ((c * l : quasiNormalizer u) : J) := by simp
    rw [this]
    exact B.mul_mem (B.inv_mem hcB) hg

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
