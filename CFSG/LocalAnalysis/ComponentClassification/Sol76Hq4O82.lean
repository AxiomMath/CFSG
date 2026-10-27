module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8E
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8ECert
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Row
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt CFSG.ComponentClassification.RankTwoClassical.ExcO8E
open CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.EvenSmallLie.OmegaEight.Cover

theorem censusChecks_e480 : CensusChecks :=
  ⟨census_arr_check, census_chain_check, census_cover_check, census_fusion_check,
    census_deriv_check⟩

section Model


theorem pow_ten_dvd_card_inf_centralizer_e480 (hC : CensusChecks) {y : Equiv.Perm (Fin 480)}
    (hy : y ∈ e480) (ho : orderOf y = 2) (hyz : y ∉ zs) :
    2 ^ 10 ∣ Nat.card ↥(e480 ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 480)))) := by
  obtain ⟨x, hx, -, g, hg, hgy⟩ := conj_classes_e480 hC hy ho hyz
  obtain ⟨-, -, h48v, h48card, h48c, h16v, h16card, h16c⟩ := chain_facts hC
  have hS : ∃ S : Subgroup (Equiv.Perm (Fin 480)),
      S ≤ e480 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 480))) ∧ 2 ^ 10 ∣ Nat.card S := by
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · refine ⟨s48, le_inf ((s_le_T s48_eq).trans (tT_le hC))
        (s_le_centralizer (by rw [s48, s48Q, certificate_originalSubgroup]) h48c), ?_⟩
      rw [← s48Q.orderCertificate_eq_card h48v, h48card]
      norm_num
    · refine ⟨s16, le_inf ((s_le_T s16_eq).trans (tT_le hC))
        (s_le_centralizer (by rw [s16, s16Q, certificate_originalSubgroup]) h16c), ?_⟩
      rw [← s16Q.orderCertificate_eq_card h16v, h16card]
      norm_num
  obtain ⟨S, hSle, hScard⟩ := hS
  have hle : S.map (MulAut.conj g⁻¹).toMonoidHom ≤
      e480 ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 480))) := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hsE, hsC'⟩ := hSle hs
    have hsC : s * x = x * s := mem_centralizer_singleton_iff.mp hsC'
    refine ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · change g⁻¹ * s * g⁻¹⁻¹ ∈ e480
      exact e480.mul_mem (e480.mul_mem (e480.inv_mem hg) hsE) (e480.inv_mem (e480.inv_mem hg))
    · change g⁻¹ * s * g⁻¹⁻¹ * y = y * (g⁻¹ * s * g⁻¹⁻¹)
      have hy' : y = g⁻¹ * x * g := by rw [← hgy]; group
      rw [hy']
      calc g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * x * g) = g⁻¹ * (s * x) * g := by group
        _ = g⁻¹ * (x * s) * g := by rw [hsC]
        _ = g⁻¹ * x * g * (g⁻¹ * s * g⁻¹⁻¹) := by group
  have hc : Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  exact (hc ▸ hScard).trans (Subgroup.card_dvd_of_le hle)

theorem exists_zElt_of_mem_ker {w : eFib} (hw : w ∈ qE.ker) : ∃ a b : Bool, w = zElt a b := by
  obtain ⟨h1, h2⟩ := mem_ker_qE.1 hw
  refine ⟨decide ((w : wPlus × wPlus).1 = zPlus), decide ((w : wPlus × wPlus).2 = zPlus), ?_⟩
  have hz : zPlus ≠ 1 := zPlus_ne_one
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rcases h1 with h | h <;> simp [zElt, h, hz.symm]
  · rcases h2 with h | h <;> simp [zElt, h, hz.symm]

theorem centralFour_O82
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hL : LieModel (Q ⧸ center Q) .POmegaPlus 4 2 1) {u v : Q} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q) (hvZ : v ∈ center Q) :
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  have hC := censusChecks_e480
  have hrow : GriessAll.GriessRow (Q ⧸ center Q) .POmegaPlus 4 2 1 :=
    GriessClassical.pomegaPlus_four_two_row (GriessNative.models_lieModel_of_classical
      (GriessNative.classical_of_lieModel hL (by decide)))
  have hZ4 : Nat.card (center Q) = 4 := by
    obtain ⟨_, φ, hφ⟩ := exists_hom_range_eq_center hQ hrow
    have hdvd := Subgroup.card_range_dvd φ
    rw [hφ] at hdvd
    have hm : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
      (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k)).trans
        (Nat.card_zmod k)
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hm, hm, hm, hm] at hdvd
    have hle : Nat.card (center Q) ≤ 4 := Nat.le_of_dvd (by decide) (hdvd.trans (by decide))
    have hge : 4 ≤ Nat.card (center Q) :=
      (four_le_card_omegaCenter huZ hvZ hu2 hv2 hu1 hv1 huv).trans
        (Subgroup.card_le_of_le fun z hz => hz.1)
    omega
  have : Group.IsPerfect Q := hQ.1
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_eFib (isPerfect_eFib' hC) hQ.1 hZ4 hL
  let ι : Q →* Equiv.Perm (Fin 480) := eHom.comp θ.toMonoidHom
  have hιinj : Function.Injective ι := eHom_injective.comp θ.injective
  have hιmem : ∀ x : Q, ι x ∈ e480 := fun x => ⟨θ x, rfl⟩
  have hcenter : ∀ x : Q, θ x ∈ qE.ker → x ∈ center Q := by
    intro x hx
    rw [← hθ] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    rw [θ.injective hzx] at hz
    exact hz
  have hzs : ∀ x : Q, x ∉ center Q → ι x ∉ zs := by
    intro x hxZ hxzs
    apply hxZ
    apply hcenter
    rcases (mem_zs_iff hC).1 hxzs with h | h | h <;>
      · have h' : eHom (θ x) = eHom (zElt _ _) := h
        rw [eHom_injective h']
        exact zElt_mem_ker _ _
  refine ⟨?_, fun x hx hxZ => ?_⟩
  ·
    obtain ⟨hx48, hx48z⟩ := (fusion_facts hC).2.1 x48 (by simp [xs])
    obtain ⟨w, hw⟩ : x48 ∈ e480 := tT_le hC (x_mem (by simp [xs]))
    refine ⟨θ.symm w, ?_, fun hZ => ?_⟩
    · rw [← orderOf_injective ι hιinj, show ι (θ.symm w) = x48 by
        change eHom (θ (θ.symm w)) = x48
        rw [MulEquiv.apply_symm_apply, hw]]
      exact hx48
    · have hk : w ∈ qE.ker := by
        rw [← hθ]
        exact ⟨θ.symm w, hZ, θ.apply_symm_apply w⟩
      obtain ⟨a, b, rfl⟩ := exists_zElt_of_mem_ker hk
      cases a <;> cases b
      · apply_fun orderOf at hw
        rw [show zElt false false = 1 from Subtype.ext (by simp [zElt]), map_one, orderOf_one,
          hx48] at hw
        omega
      · exact hx48z (by rw [← hw]; exact (mem_zs_iff hC).2 (Or.inr (Or.inl rfl)))
      · exact hx48z (by rw [← hw]; exact (mem_zs_iff hC).2 (Or.inl rfl))
      · exact hx48z (by rw [← hw]; exact (mem_zs_iff hC).2 (Or.inr (Or.inr rfl)))
  ·
    have h10 : 2 ^ 10 ∣ Nat.card (centralizer ({x} : Set Q)) := by
      have hdvd := pow_ten_dvd_card_inf_centralizer_e480 hC (hιmem x)
        (by rw [orderOf_injective ι hιinj]; exact hx) (hzs x hxZ)
      have hmap : (centralizer ({x} : Set Q)).map ι =
          e480 ⊓ centralizer ({ι x} : Set (Equiv.Perm (Fin 480))) := by
        ext y
        constructor
        · rintro ⟨g, hg, rfl⟩
          refine ⟨hιmem g, mem_centralizer_singleton_iff.mpr ?_⟩
          rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hg]
        · rintro ⟨⟨w, rfl⟩, hy'⟩
          have hy := mem_centralizer_singleton_iff.mp hy'
          refine ⟨θ.symm w, mem_centralizer_singleton_iff.mpr ?_, ?_⟩
          · apply hιinj
            rw [map_mul, map_mul]
            change eHom (θ (θ.symm w)) * ι x = ι x * eHom (θ (θ.symm w))
            rw [MulEquiv.apply_symm_apply]
            exact hy
          · change eHom (θ (θ.symm w)) = eHom w
            rw [MulEquiv.apply_symm_apply]
      rw [← hmap, Subgroup.card_map_of_injective hιinj] at hdvd
      exact hdvd
    have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h10
    rw [hZ4, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.single_eq_same]
    omega

end Model

end CFSG.ComponentClassification.Sol76T13.Hq4
