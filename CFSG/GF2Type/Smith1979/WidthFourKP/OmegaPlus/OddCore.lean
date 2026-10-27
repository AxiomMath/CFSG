module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.FanoCount
public import CFSG.LargeExtraspecial.S7Seven
public import CFSG.Adapters.WholeGroupLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_4_8_inf_centralizer (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {F : Subgroup S.O} (hFM : F ≤ S.Mbar) (hodd : Odd (Nat.card F))
    (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {v : S.O} (hv : v ∈ S.Lbar g)
    (hv1 : v ≠ 1) :
    F ⊓ centralizer ({v} : Set S.O) = ⊥ ∨
      Nat.card (F ⊓ centralizer ({v} : Set S.O) : Subgroup S.O) = 3 ∨
      (Nat.card (F ⊓ centralizer ({v} : Set S.O) : Subgroup S.O) = 9 ∧
        Nat.card (S.Lbar g) = 8 ∧
        ∀ s ∈ S.Lbar g,
          (∀ x ∈ F ⊓ centralizer ({v} : Set S.O), s * x = x * s) → s = 1 ∨ s = v) := by
  by_cases hbot : F ⊓ centralizer ({v} : Set S.O) = ⊥
  · exact Or.inl hbot
  have hodd' : Odd (Nat.card (F ⊓ centralizer ({v} : Set S.O) : Subgroup S.O)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  rcases timmesfeld_4_8_M H hNo C hv hv1 (inf_le_left.trans hFM) hodd' hbot
      (fun x hx => mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2)
      (fun s hs x hx => conj_mem_inf_centralizer H hnorm hv hs hx)
      (fun x hx hc => eq_one_of_mem_of_commute H hodd' hx hc) with h3 | ⟨h9, h8, hCL⟩
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr ⟨h9, h8, hCL⟩)

theorem card_inf_centralizer_dvd_nine (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {F : Subgroup S.O} (hFM : F ≤ S.Mbar) (hodd : Odd (Nat.card F))
    (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {v : S.O} (hv : v ∈ S.Lbar g)
    (hv1 : v ≠ 1) : Nat.card (F ⊓ centralizer ({v} : Set S.O) : Subgroup S.O) ∣ 9 := by
  rcases timmesfeld_4_8_inf_centralizer H hNo C hFM hodd hnorm hv hv1 with hbot | h3 | ⟨h9, -⟩
  · rw [hbot]
    simp
  · rw [h3]
    norm_num
  · rw [h9]

theorem four_le_card_inf_centralizer_of_isCyclic {X : Type*} [Group X] [Finite X]
    (F L : Subgroup X) (hF9 : Nat.card F = 9) (hL8 : Nat.card L = 8)
    (hLF : L ≤ normalizer (F : Set X)) (hcyc : IsCyclic F) :
    4 ≤ Nat.card ↥(L ⊓ centralizer (F : Set X)) := by
  classical
  letI : IsCyclic F := hcyc
  have haut : Nat.card (MulAut F) = 6 := by
    rw [IsCyclic.card_mulAut, hF9]
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
      Nat.totient_prime_pow Nat.prime_three (by norm_num)]
    norm_num
  let incl : L →* Subgroup.normalizer (F : Set X) := Subgroup.inclusion hLF
  let psi : L →* MulAut F := F.normalizerMonoidHom.comp incl
  have hker_mul : Nat.card psi.ker * Nat.card psi.range = 8 := by
    rw [Subgroup.card_ker_mul_card_range psi, hL8]
  have hrange_dvd6 : Nat.card psi.range ∣ 6 := by
    rw [← haut]
    exact Subgroup.card_subgroup_dvd_card psi.range
  have hrange_dvd8 : Nat.card psi.range ∣ 8 :=
    ⟨Nat.card psi.ker, by rw [mul_comm]; exact hker_mul.symm⟩
  have hrange_dvd2 : Nat.card psi.range ∣ 2 := by
    have h := Nat.dvd_gcd hrange_dvd8 hrange_dvd6
    rwa [show Nat.gcd 8 6 = 2 by norm_num] at h
  have hrange_le : Nat.card psi.range ≤ 2 := Nat.le_of_dvd (by norm_num) hrange_dvd2
  have hker_ge : 4 ≤ Nat.card psi.ker := by
    have hpos : 0 < Nat.card psi.range := Nat.card_pos
    nlinarith
  have hker_le : psi.ker.map L.subtype ≤ L ⊓ Subgroup.centralizer (F : Set X) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_inf.mpr ⟨s.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : F.normalizerMonoidHom (incl s) = 1 := MonoidHom.mem_ker.mp hs
    have h2 : ((F.normalizerMonoidHom (incl s)) ⟨z, hz⟩ : X) = z := by
      rw [h1]
      rfl
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] at h2
    calc
      z * (s : X) = ((s : X) * z * (s : X)⁻¹) * (s : X) := by rw [h2]
      _ = (s : X) * z := by group
  have hcard_le : Nat.card psi.ker ≤ Nat.card ↥(L ⊓ Subgroup.centralizer (F : Set X)) := by
    rw [← Subgroup.card_map_of_injective L.subtype_injective]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hker_le)
  omega

theorem pow_three_of_mem_inf_centralizer (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {F : Subgroup S.O} (hFM : F ≤ S.Mbar) (hodd : Odd (Nat.card F))
    (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {v : S.O} (hv : v ∈ S.Lbar g)
    (hv1 : v ≠ 1) {x : S.O} (hx : x ∈ F ⊓ centralizer ({v} : Set S.O)) : x ^ 3 = 1 := by
  classical
  let K : Subgroup S.O := F ⊓ centralizer ({v} : Set S.O)
  have hLF : S.Lbar g ≤ Subgroup.normalizer (K : Set S.O) :=
    Subgroup.le_normalizer_iff.mpr fun s hs y hy => conj_mem_inf_centralizer H hnorm hv hs hy
  rcases timmesfeld_4_8_inf_centralizer H hNo C hFM hodd hnorm hv hv1 with hbot | h3 | ⟨h9, h8, hCL⟩
  · have hx1 : x = 1 := Subgroup.mem_bot.mp (hbot ▸ hx)
    rw [hx1, one_pow]
  · have hx3 : x ^ Nat.card K = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard K hx)
    rwa [h3] at hx3
  · have hnotcyc : ¬ IsCyclic ↥K := by
      intro hcyc
      have h4 := four_le_card_inf_centralizer_of_isCyclic K (S.Lbar g) h9 h8 hLF hcyc
      have h2 : Nat.card ↥(S.Lbar g ⊓ Subgroup.centralizer (K : Set S.O)) ≤ 2 := by
        refine S5.card_le_two_of_subset (t := v) ?_
        intro s hs
        exact hCL s (Subgroup.mem_inf.mp hs).1
          (fun y hy => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs).2 y hy).symm)
      omega
    have hexp : Monoid.exponent ↥K = 3 :=
      (not_isCyclic_iff_exponent_eq_prime Nat.prime_three (by rw [h9]; norm_num)).mp hnotcyc
    have h := Subgroup.pow_exponent_eq_one (H := K) hx
    rwa [hexp] at h

theorem mem_Obar_of_commute_of_isNilpotent (hE : timmesfeldLayer S.Mbar = ⊥)
    (hnil : Group.IsNilpotent (timmesfeldOddCore S.Mbar)) {x : S.O} (hx : x ∈ S.Mbar)
    (hc : ∀ y ∈ S7.Obar S, x * y = y * x) : x ∈ S7.Obar S := by
  have hge : timmesfeldOddCore S.Mbar ≤ timmesfeldFitting S.Mbar := by
    refine le_sSup ⟨timmesfeldOddCore_normal S.Mbar, ?_⟩
    exact hnil
  have hF : timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar := by
    rw [timmesfeldFStar, hE, sup_bot_eq]
    exact le_antisymm (fitting_le_oddCore S) hge
  have hx' : (⟨x, hx⟩ : S.Mbar) ∈
      centralizer (timmesfeldFStar S.Mbar : Set S.Mbar) := by
    rw [hF, mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hc (y : S.O) ⟨y, hy, rfl⟩).symm
  have h := CFSG.Adapters.centralizer_timmesfeldFStar_le (G := S.Mbar) hx'
  rw [hF] at h
  exact ⟨⟨x, hx⟩, h, rfl⟩

theorem eq_one_of_mem_Lbar_of_commute_Obar (H : Hyp4 S g) (hE : timmesfeldLayer S.Mbar = ⊥)
    (hnil : Group.IsNilpotent (timmesfeldOddCore S.Mbar)) {s : S.O} (hs : s ∈ S.Lbar g)
    (hc : ∀ y ∈ S7.Obar S, s * y = y * s) : s = 1 := by
  have hsM : s ∈ S.Mbar := S.Lbar_le_Mbar g hs
  have hsO : s ∈ S7.Obar S := mem_Obar_of_commute_of_isNilpotent hE hnil hsM hc
  have hss : s * s = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem hs
  have hdvd2 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hss)
  have hdvdO : orderOf s ∣ Nat.card (S7.Obar S) := Subgroup.orderOf_dvd_natCard _ hsO
  have hoddO : Odd (Nat.card (S7.Obar S)) := by
    rw [S7.card_Obar]
    exact odd_card_timmesfeldOddCore S.Mbar
  have hgcd : Nat.gcd 2 (Nat.card (S7.Obar S)) = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hoddO)
  have hdvd1 : orderOf s ∣ 1 := by
    have h := Nat.dvd_gcd hdvd2 hdvdO
    rwa [hgcd] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

theorem card_oddCore_of_layer_eq_bot (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (hE : timmesfeldLayer S.Mbar = ⊥) :
    Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3 ∨
      (Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 4 ∧
        ∃ p ∈ S.Lbar g, p ≠ 1 ∧ ∀ y ∈ S7.Obar S, p * y = y * p → y = 1) := by
  classical
  have hObarOdd : Odd (Nat.card (S7.Obar S)) := by
    rw [S7.card_Obar]
    exact S5.odd_card_timmesfeldOddCore S.Mbar
  have hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ S7.Obar S, s * x * s⁻¹ ∈ S7.Obar S :=
    fun s hs x hx => S7.conj_mem_Obar (S.Lbar_le_Mbar g hs) hx
  have h9 : ∀ s ∈ S.Lbar g, s ≠ 1 →
      Nat.card (S7.Obar S ⊓ centralizer ({s} : Set S.O) : Subgroup S.O) ∣ 9 :=
    fun s hs hs1 =>
      card_inf_centralizer_dvd_nine H hNo C S7.Obar_le_Mbar hObarOdd hnorm hs hs1
  have hnil : Group.IsNilpotent (timmesfeldOddCore S.Mbar) := by
    obtain ⟨a, haL, b, hbL, ha1, hb1, hab⟩ :=
      S5.exists_ne_one_ne_one_ne (A := S.Lbar g) (by
        have h := S5.four_le_card_Lbar H C
        omega)
    have ha2 : a * a = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem haL
    have hb2 : b * b = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem hbL
    have habc : a * b = b * a := S4.Lbar_comm S H.conj_mem haL hbL
    have habL : a * b ∈ S.Lbar g := (S.Lbar g).mul_mem haL hbL
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      calc
        a = a * 1 := (mul_one a).symm
        _ = a * (a * b) := by rw [h]
        _ = (a * a) * b := by rw [mul_assoc]
        _ = b := by rw [ha2, one_mul]
    obtain ⟨n, hn⟩ := card_eq_three_pow_of_four hObarOdd ha2 hb2 habc
      (hnorm a haL) (hnorm b hbL) (h9 a haL ha1) (h9 b hbL hb1) (h9 (a * b) habL hab1)
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hcard3 : Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ n := by
      rw [← S7.card_Obar]
      exact hn
    exact IsPGroup.isNilpotent (IsPGroup.of_card (p := 3) (n := n) hcard3)
  have hL8 : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  have hL2 : ∀ s ∈ S.Lbar g, s * s = 1 :=
    fun s hs => S4.mul_self_of_mem_Lbar S H.conj_mem hs
  have hLc : ∀ s ∈ S.Lbar g, ∀ s' ∈ S.Lbar g, s * s' = s' * s :=
    fun s hs s' hs' => S4.Lbar_comm S H.conj_mem hs hs'
  have hCF : ∀ x ∈ S7.Obar S, (∀ s ∈ S.Lbar g, s * x = x * s) → x = 1 :=
    fun x hx hc => S5.eq_one_of_mem_of_commute H hObarOdd hx hc
  have hfaith : ∀ s ∈ S.Lbar g, (∀ x ∈ S7.Obar S, s * x = x * s) → s = 1 :=
    fun s hs hc => eq_one_of_mem_Lbar_of_commute_Obar H hE hnil hs hc
  have hmain := card_eq_of_elemTwo (X := S.O) (L := S.Lbar g) (F := S7.Obar S)
    hL8 hL2 hLc hObarOdd hnorm hCF hfaith h9
  rw [S7.card_Obar] at hmain
  exact hmain

end CFSG.GF2Type.Smith1979.OmegaPlus

end
