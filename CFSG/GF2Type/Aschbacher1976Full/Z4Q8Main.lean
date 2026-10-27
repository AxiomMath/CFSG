module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8WData

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Sylow

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint CFSG.EvenSporadicStandard.Finkelstein77
open CFSG.Open (WreathedTwoGroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_Fz_le {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G}
    (hh : h ∈ Hz z) (hc : ∀ f ∈ Fz z, h * f = f * h) : h ∈ Fz z := by
  have hmem : (⟨h, hh⟩ : ↥(Hz z)) ∈
      Subgroup.centralizer ((generalizedFitting ↥(Hz z) : Subgroup ↥(Hz z)) : Set ↥(Hz z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnF : (n : G) ∈ Fz z := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    apply Subtype.ext
    exact (hc n hnF).symm
  have hgf := centralizer_generalizedFitting_le ↥(Hz z) hmem
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩, hgf, rfl⟩

theorem conj_z_ne_z {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G}
    (hh0 : (Zc z).map (MulAut.conj h).toMonoidHom ≠ Zc z) : h * z * h⁻¹ ≠ z := by
  intro hc
  have hH : h ∈ Hz z := mem_Hz_of_conj_mem_Zc hZ hz (by rw [hc]; exact z_mem_Zc hZ hz)
  have hHi : h⁻¹ ∈ Hz z := Subgroup.inv_mem _ hH
  apply hh0
  rw [map_conj_eq_conjugate, conjugate_Zc_eq hZ hz hHi]

theorem conj_gen_not_mem_Fz {z h k : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2)
    (hk2 : k ^ 2 = z) (hh0 : (Zc z).map (MulAut.conj h).toMonoidHom ≠ Zc z) :
    h * k * h⁻¹ ∉ Fz z := by
  intro hyF
  have h1 := sq_mem_zpowers_Fz hZ hz hyF
  have h2 : (h * k * h⁻¹) ^ 2 = h * z * h⁻¹ := by
    rw [conj_pow, hk2]
  rw [h2] at h1
  rcases mem_zpowers_two hz h1 with h3 | h3
  · have hz1 : z = 1 := by
      calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
        _ = 1 := by rw [h3]; group
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact conj_z_ne_z hZ hz hh0 h3

theorem isSylow_of_T {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {T : Subgroup G}
    (hTH : T ≤ Hz z) (hFT : Fz z ≤ T)
    (hmaxH : ∀ Q : Subgroup G, Q ≤ Hz z → IsPGroup 2 ↥Q → T ≤ Q → Q = T) :
    ∀ S : Subgroup G, IsPGroup 2 ↥S → T ≤ S → S = T := by
  intro S hS hTS
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hzT : ∀ t ∈ T, z * t = t * z := fun t ht => (Subgroup.mem_centralizer_iff.mp (hTH ht)) z
    (Set.mem_singleton z)
  have hzF : z ∈ T := hFT ((mem_Zc_iff hZ hz).mp (z_mem_Zc hZ hz)).1
  set T' : Subgroup ↥S := T.subgroupOf S with hT'
  have hT'top : T' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm ?_ hTS
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥S) ∈ T' := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent T' hT'top)
  set g : G := (x : G) with hg
  have hgN : ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro t ht
    have hn : (⟨t, hTS ht⟩ : ↥S) ∈ T' := Subgroup.mem_subgroupOf.mpr ht
    have := (Subgroup.mem_normalizer_iff.mp hxN ⟨t, hTS ht⟩).mp hn
    exact Subgroup.mem_subgroupOf.mp this
  have hgN' : ∀ t ∈ T, g⁻¹ * t * g ∈ T := by
    intro t ht
    have hn : x⁻¹ * (⟨t, hTS ht⟩ : ↥S) * x ∈ T' := by
      rw [Subgroup.mem_normalizer_iff] at hxN
      refine (hxN _).mpr ?_
      have e : x * (x⁻¹ * (⟨t, hTS ht⟩ : ↥S) * x) * x⁻¹ = ⟨t, hTS ht⟩ := by group
      rw [e]
      exact Subgroup.mem_subgroupOf.mpr ht
    exact Subgroup.mem_subgroupOf.mp hn
  have hc_mem : g * z * g⁻¹ ∈ T := hgN z hzF
  have hc_cent : ∀ t ∈ T, t * (g * z * g⁻¹) = (g * z * g⁻¹) * t := by
    intro t ht
    have h1 := hzT _ (hgN' t ht)
    calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = (g * z * g⁻¹) * t := by group
  have hc_F : ∀ f ∈ Fz z, (g * z * g⁻¹) * f = f * (g * z * g⁻¹) := fun f hf =>
    (hc_cent f (hFT hf)).symm
  have hc_H : g * z * g⁻¹ ∈ Hz z := hTH hc_mem
  have hc_inF : g * z * g⁻¹ ∈ Fz z := centralizer_Fz_le hZ hz hc_H hc_F
  have hc_Zc : g * z * g⁻¹ ∈ Zc z := (mem_Zc_iff hZ hz).mpr ⟨hc_inF, hc_F⟩
  have hgH : g ∈ Hz z := mem_Hz_of_conj_mem_Zc hZ hz hc_Zc
  have hQp : IsPGroup 2 ↥(S ⊓ Hz z) := by
    intro q
    obtain ⟨k, hk⟩ := hS ⟨q.1, (Subgroup.mem_inf.mp q.2).1⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hTQ : T ≤ S ⊓ Hz z := le_inf hTS hTH
  have hQT := hmaxH (S ⊓ Hz z) inf_le_right hQp hTQ
  have hgT : g ∈ T := by
    have hgSH : g ∈ S ⊓ Hz z := Subgroup.mem_inf.mpr ⟨x.2, hgH⟩
    rw [hQT] at hgSH
    exact hgSH
  exact hxT (Subgroup.mem_subgroupOf.mpr hgT)

theorem sylow_structure [IsSimpleGroup G] (hdih : ∀ x : G, orderOf x = 4 →
      WeaklyClosedInNormalizer (Subgroup.zpowers x) →
      CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo G ∨
        CFSG.ComponentClassification.AschbacherKnownGroup.HasSemidihedralSylowTwo G)
    {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    Nat.card ↥(Hz z) = 96 ∧ ∃ T : Subgroup G, IsPGroup 2 ↥T ∧
      (∀ S : Subgroup G, IsPGroup 2 ↥S → T ≤ S → S = T) ∧ Nat.card ↥T = 32 ∧
      Nonempty (↥T ≃* WreathedTwoGroup 2) := by
  obtain ⟨k, hkZ, hk4, hkZp, hk2⟩ := exists_gen_Zc hZ hz
  obtain ⟨h0, hh0le, hh0ne⟩ := exists_conj_le_Hz hdih hZ hz hk4 hkZp
  have hcycZc : IsCyclic ↥(Zc z) := by
    obtain ⟨Z', A', hZeq, hcyc', -⟩ := unpack hZ hz
    rw [hZeq]
    exact hcyc'
  have hy4 : orderOf (h0 * k * h0⁻¹) = 4 := by
    rw [← hk4]
    exact orderOf_injective (MulAut.conj h0).toMonoidHom (MulAut.conj h0).injective k
  have hyZh : h0 * k * h0⁻¹ ∈ (Zc z).map (MulAut.conj h0).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨k, hkZ, rfl⟩
  obtain ⟨T, hTH, hTp, hTmax, hFT, hZhT⟩ := exists_sylow_containing hZ hz hh0le
  have hyT : h0 * k * h0⁻¹ ∈ T := hZhT hyZh
  have hZT : Zc z ≤ T := fun x hx => hFT ((mem_Zc_iff hZ hz).mp hx).1
  set y : G := h0 * k * h0⁻¹ with hydef
  have hcomm : k * y = y * k := commute_Zc_map hZ hz hTp hZT hZhT k hkZ y hyZh
  have hyF : y ∉ Fz z := conj_gen_not_mem_Fz hZ hz hk2 hh0ne
  obtain ⟨hH96, hT32⟩ := card_Hz_and_T hZ hz hTH hTp hFT hyT hyF
  have hTcard : Nat.card ↥T = 2 * Nat.card ↥(Fz z) := by rw [hT32, card_Fz hZ hz]
  have htF : y ^ 2 ∈ Fz z := sq_mem_of_card_two hZ hz hFT hTH hTcard hyT hyF
  have htz : y ^ 2 ≠ z := by
    intro h
    apply conj_z_ne_z hZ hz hh0ne
    calc h0 * z * h0⁻¹ = h0 * k ^ 2 * h0⁻¹ := by rw [hk2]
      _ = (h0 * k * h0⁻¹) ^ 2 := conj_pow.symm
      _ = z := h
  have hy4' : y ^ 4 = 1 := by
    rw [← hy4]
    exact pow_orderOf_eq_one y
  have hy2ne1 : y ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hy4] at hd
    norm_num at hd
  have hKY : Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥ :=
    zpowers_inf_eq_bot hZ hz hkZp hy4 hyF htF htz
  have hA16 : Nat.card ↥(Subgroup.zpowers k ⊔ Subgroup.zpowers y) = 16 :=
    card_A hcomm hk4 hy4 hKY
  have hAT : Subgroup.zpowers k ⊔ Subgroup.zpowers y ≤ T :=
    sup_le (Subgroup.zpowers_le.mpr (hZT hkZ)) (Subgroup.zpowers_le.mpr hyT)
  have hAnorm : ((Subgroup.zpowers k ⊔ Subgroup.zpowers y).subgroupOf T).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have h1 := Subgroup.index_mul_card (H := (Subgroup.zpowers k ⊔ Subgroup.zpowers y).subgroupOf T)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv, hA16, hT32] at h1
    omega
  have hAsub : ∀ g ∈ T, ∀ a ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y,
      g * a * g⁻¹ ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y := by
    intro g hg a ha
    have ha' : (⟨a, hAT ha⟩ : ↥T) ∈ (Subgroup.zpowers k ⊔ Subgroup.zpowers y).subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr ha
    have := hAnorm.conj_mem _ ha' ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hAinv : ∀ x ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y, x ^ 2 = 1 →
      x = 1 ∨ x = z ∨ x = y ^ 2 ∨ x = z * y ^ 2 := fun x hx hx2 =>
    involution_of_A hZ hz hcomm hkZ hkZp hy4 hKY hx hx2
  have hAcomm : ∀ a ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y,
      ∀ b ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y, a * b = b * a := by
    refine comm_sup_of ?_ ?_ ?_
    · intro c hc c' hc'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
      exact (Commute.zpow_zpow_self k i j).eq
    · intro d hd d' hd'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd'
      exact (Commute.zpow_zpow_self y i j).eq
    · intro c hc d hd
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      exact ((show Commute k y from hcomm).zpow_zpow i j).eq
  have hsex : ∃ s ∈ T, s ∉ Subgroup.zpowers k ⊔ Subgroup.zpowers y := by
    by_contra hcon
    push Not at hcon
    have heq := Subgroup.eq_of_le_of_card_ge (H := T) (K := Subgroup.zpowers k ⊔ Subgroup.zpowers y)
      hcon (by rw [hA16, hT32]; norm_num)
    have := congrArg (fun H : Subgroup G => Nat.card ↥H) heq
    simp only [hA16, hT32] at this
    omega
  obtain ⟨s, hsT, hsA⟩ := hsex
  have hcard_T_A : Nat.card ↥T = 2 * Nat.card ↥(Subgroup.zpowers k ⊔ Subgroup.zpowers y) := by
    rw [hT32, hA16]
  have hcoset : ∀ x ∈ T, x ∉ Subgroup.zpowers k ⊔ Subgroup.zpowers y →
      s⁻¹ * x ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y := fun x hx hxA =>
    inv_mul_mem_of_card_two hAT hcard_T_A hAnorm hx hsT hxA hsA
  have hs2A : s ^ 2 ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y := by
    by_contra hcon
    have h1 := inv_mul_mem_of_card_two hAT hcard_T_A hAnorm (T.pow_mem hsT 2) hsT hcon hsA
    apply hsA
    have e : s⁻¹ * s ^ 2 = s := by rw [sq]; group
    rw [← e]
    exact h1
  have hzT : ∀ g ∈ T, z * g = g * z := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hTH ht)) z (Set.mem_singleton z)
  have hFnc : ∃ f ∈ Fz z, f * y ^ 2 ≠ y ^ 2 * f := by
    by_contra hcon
    push Not at hcon
    have hmemZ : y ^ 2 ∈ Zc z :=
      (mem_Zc_iff hZ hz).mpr ⟨htF, fun f hf => (hcon f hf).symm⟩
    have hsq : (y ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hy4'
    rcases involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hmemZ hsq with h | h
    · exact hy2ne1 h
    · exact htz h
  have hy2A : y ^ 2 ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2)
  have hst : s * y ^ 2 * s⁻¹ = z * y ^ 2 :=
    conj_sq_eq hsT hsA hAsub hAinv hAcomm hy2A hzT hFT hFnc hcoset hy4' hy2ne1 htz
  obtain ⟨s', hs'T, hWD⟩ := wdata_exists hcomm hk4 hy4 hk2 hKY hsT hyT hsA hs2A hst hAsub
  have hvT : s * y * s⁻¹ ∈ T := T.mul_mem (T.mul_mem hsT hyT) (T.inv_mem hsT)
  have hwr : Nonempty (↥T ≃* WreathedTwoGroup 2) := wreath_iso hT32 hyT hvT hs'T hWD
  exact ⟨hH96, T, hTp, isSylow_of_T hZ hz hTH hFT hTmax, hT32, hwr⟩

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
