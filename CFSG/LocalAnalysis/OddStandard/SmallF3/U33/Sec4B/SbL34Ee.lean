module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ea
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {Λ : Type} [Group Λ] [Finite Λ] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] {ι : Λ →* (E ≃ₗ[ZMod 2] E)} {P W : Subgroup Λ} {r s : Λ}

theorem card_W_le_sixteen (h : Crit ι P W r s) : Nat.card W ≤ 16 := by
  let t : ↥W := ⟨s, h.s_mem⟩
  have ht2 : t ^ 2 = 1 := by
    apply W.subtype_injective
    rw [map_pow, map_one]
    simpa [t, pow_two] using h.s_sq
  have ht1 : t ≠ 1 := by
    intro ht
    have hs1 : s = 1 := by
      have h2 : (t : Λ) = 1 := by rw [ht]; rfl
      simpa [t] using h2
    have hr : r = r⁻¹ := by
      have hc := h.s_conj
      rw [hs1, one_mul, inv_one, mul_one] at hc
      exact hc
    have hr2 : r * r = 1 := by
      have hc := congrArg (fun x : Λ => r * x) hr
      rwa [mul_inv_cancel] at hc
    have hr1 : r = 1 := by
      have h3 : r ^ 3 = r := by rw [pow_succ, pow_two, hr2, one_mul]
      rw [← h3, h.r_cube]
    exact h.r_ne hr1
  have hDsub : (Subgroup.centralizer ({s} : Set Λ) ⊓ W).subgroupOf W =
      Subgroup.centralizer ({t} : Set ↥W) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, _⟩
      exact Subtype.ext hx
    · intro hx
      exact ⟨congrArg (fun y : ↥W => (y : Λ)) hx, x.2⟩
  have hcard_eq : Nat.card (Subgroup.centralizer ({t} : Set ↥W)) =
      Nat.card ↥(Subgroup.centralizer ({s} : Set Λ) ⊓ W) := by
    rw [← hDsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.centralizer ({s} : Set Λ) ⊓ W ≤ W)).toEquiv
  have hC : Nat.card (Subgroup.centralizer ({t} : Set ↥W)) ≤ 4 := by
    rw [hcard_eq, h.cent]
  obtain ⟨C, hCcyc, hCidx⟩ :=
    CFSG.EvenSporadicStandard.Fin76b.exists_cyclic_index_le_two h.W_pgroup ht2 ht1 hC
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := ↥C)).mp hCcyc
  let cc : ↥W := (g : ↥W)
  have hord : orderOf cc = Nat.card C := by
    have h1 : orderOf cc = orderOf g := by
      show orderOf (g : ↥W) = orderOf g
      exact orderOf_injective C.subtype C.subtype_injective g
    rw [h1, hg]
  have hCpg : IsPGroup 2 C := h.W_pgroup.to_subgroup C
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥C)).mp hCpg
  have horda : orderOf cc = 2 ^ a := by rw [hord, ha]
  have hcpow : cc ^ 2 ^ a = 1 := by rw [← horda]; exact pow_orderOf_eq_one cc
  have hx8 : (cc : Λ) ^ 8 = 1 := by
    have hxpow : (cc : Λ) ^ 2 ^ a = 1 := by
      have h := map_pow W.subtype cc (2 ^ a)
      rw [hcpow, map_one] at h
      exact h.symm
    have hι : (ι (cc : Λ)) ^ 2 ^ a = 1 := by
      have h := map_pow ι (cc : Λ) (2 ^ a)
      rw [hxpow, map_one] at h
      exact h.symm
    have h8 : (ι (cc : Λ)) ^ 8 = 1 :=
      pow_eight_eq_one_of_finrank_le (by rw [h.dim]; norm_num) (ι (cc : Λ)) hι
    exact h.inj (by rw [map_pow, h8, map_one])
  have hdvd : orderOf (cc : Λ) ∣ 8 := orderOf_dvd_iff_pow_eq_one.mpr hx8
  have hord_val : orderOf (cc : Λ) = orderOf cc :=
    orderOf_injective W.subtype W.subtype_injective cc
  have hC8 : Nat.card C ∣ 8 := by rw [← hord, ← hord_val]; exact hdvd
  have hCle8 : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hC8
  calc Nat.card W = Nat.card C * C.index := (Subgroup.card_mul_index C).symm
    _ ≤ 8 * 2 := Nat.mul_le_mul hCle8 hCidx
    _ = 16 := by norm_num

theorem exists_normal_four (h : Crit ι P W r s) :
    ∃ Z : Subgroup Λ, Z ≤ P ∧ Z.Normal ∧ Nat.card Z = 4 ∧ ¬ 2 ∣ Z.relIndex P := by
  haveI := h.normal
  have hnil : Group.IsNilpotent ↥P := isNilpotent_of_fpf P r h.r_cube h.fpf
  obtain ⟨Z, hZP, hZn, hZpg, hZidx⟩ := exists_normal_sylow P hnil 2
  have hr3 : r * r * r = 1 := by rw [← h.r_cube, pow_succ, pow_two]
  have hmod : Nat.card Z ≡ 1 [MOD 3] :=
    CFSG.OddStandard.SmallF3.HarrisU33.L34Z.card_modEq_one_of_conj_fpf Z r hr3
      (fun b hb => hZn.conj_mem b hb r)
      (fun b hb hcomm => h.fpf b (hZP hb)
        (by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]))
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2) (G := ↥W)).mp h.W_pgroup
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Z)).mp hZpg
  have hsub_eq : Nat.card (Z.subgroupOf P) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hPZ : Nat.card Z * Z.relIndex P = Nat.card P := by
    rw [show Z.relIndex P = (Z.subgroupOf P).index from rfl, ← hsub_eq]
    exact Subgroup.card_mul_index (Z.subgroupOf P)
  have heq : 2 ^ b * W.index = 2 ^ (a + 1) * (3 * Z.relIndex P) := by
    rw [← hb, Subgroup.card_mul_index W, h.card_index, ← hPZ, ha, pow_succ]
    ring
  have huodd : Odd W.index :=
    Nat.not_even_iff_odd.mp (fun he => h.W_index (even_iff_two_dvd.mp he))
  have hvodd : Odd (Z.relIndex P) :=
    Nat.not_even_iff_odd.mp (fun he => hZidx (even_iff_two_dvd.mp he))
  have hodd3v : Odd (3 * Z.relIndex P) := (show Odd 3 by decide).mul hvodd
  have hcop1 : Nat.Coprime (2 ^ b) (3 * Z.relIndex P) :=
    (Nat.coprime_two_left.mpr hodd3v).pow_left b
  have hcop2 : Nat.Coprime (2 ^ (a + 1)) W.index :=
    (Nat.coprime_two_left.mpr huodd).pow_left (a + 1)
  have hle1 : b ≤ a + 1 := by
    have hdiv : 2 ^ b ∣ 2 ^ (a + 1) * (3 * Z.relIndex P) :=
      heq ▸ dvd_mul_right (2 ^ b) W.index
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop1.dvd_of_dvd_mul_right hdiv)
  have hle2 : a + 1 ≤ b := by
    have hdiv : 2 ^ (a + 1) ∣ 2 ^ b * W.index :=
      heq.symm ▸ dvd_mul_right (2 ^ (a + 1)) (3 * Z.relIndex P)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop2.dvd_of_dvd_mul_right hdiv)
  have hb_eq : b = a + 1 := le_antisymm hle1 hle2
  have hWZ : Nat.card W = 2 * Nat.card Z := by
    rw [hb, ha, hb_eq, pow_succ]
    ring
  have hW16 : Nat.card W ≤ 16 := card_W_le_sixteen h
  have hZle8 : Nat.card Z ≤ 8 := by omega
  have hZ_cases : Nat.card Z = 1 ∨ Nat.card Z = 4 := by
    have ha3 : a ≤ 3 := by
      have hh : 2 ^ a ≤ 2 ^ 3 := by rw [← ha]; exact hZle8
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hh
    interval_cases a
    · left; rw [ha]; norm_num
    · exfalso; rw [ha] at hmod; norm_num at hmod
    · right; rw [ha]; norm_num
    · exfalso; rw [ha] at hmod; norm_num at hmod
  have h4dvd : 4 ∣ Nat.card W := by
    have hh := Subgroup.card_dvd_of_le
      (inf_le_right : Subgroup.centralizer ({s} : Set Λ) ⊓ W ≤ W)
    rwa [h.cent] at hh
  have hZ4 : Nat.card Z = 4 := by
    rcases hZ_cases with h1 | h4
    · exfalso
      rw [hWZ, h1] at h4dvd
      norm_num at h4dvd
    · exact h4
  exact ⟨Z, hZP, hZn, hZ4, hZidx⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
