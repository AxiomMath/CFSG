module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveCenter
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_mem_ne_one_mem_centralizer {p : ℕ} [Fact p.Prime] {P X : Subgroup G}
    (hP : IsPGroup p P) (hXP : X ≤ P) (hnorm : P ≤ normalizer (X : Set G)) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ x ∈ centralizer (P : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : (X.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr hnorm
  have hY : X.subgroupOf P ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_of_le_iff_left_eq_bot hXP]
    exact hX
  obtain ⟨⟨a, haX, haZ⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hY)
  refine ⟨a, haX, fun h1 => ha1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨g, hg⟩)

namespace Hyp

variable {fr : JankoFrame G z}

theorem F_le_normalizer_M (_h : Hyp fr) : fr.F ≤ normalizer (fr.M : Set G) :=
  fr.F_le_centralizer.trans (le_normalizer_oddCoreOf _)

theorem card_centralizer_P₁ (h : Hyp fr) :
    Nat.card (centralizer (fr.P₁ : Set G)) = 3 ^ 5 * 720 := by
  rw [h.p10.centralizer_P₁, sup_comm, card_sup_of_inf_eq_bot h.F_le_normalizer_M
    (by rw [inf_comm]; exact h.p10.M_inf_F), fr.card_F, h.p10.card_M]
  ring

theorem card_centralizer_of_isConj_s₁ (h : Hyp fr) {y : G} (hy : IsConj y fr.s₁) :
    Nat.card (centralizer ({y} : Set G)) = 3 ^ 5 * 720 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hy.symm
  have := card_centralizer_inf_conj c fr.s₁ fr.s₁
  rw [inf_idem, inf_idem, ← h.centralizer_P₁_eq] at this
  rw [this, h.card_centralizer_P₁]

theorem isPGroup_M (h : Hyp fr) : IsPGroup 3 fr.M := IsPGroup.of_card h.p10.card_M

theorem conj_s₁_not_mem_Mbar (h : Hyp fr) (g : G) : g * fr.s₁ * g⁻¹ ∉ fr.Mbar := by
  intro hMb
  have hne : g * fr.s₁ * g⁻¹ ≠ 1 := by
    intro h1
    apply h.s₁_ne_one
    calc fr.s₁ = g⁻¹ * (g * fr.s₁ * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  exact h.p7.not_isConj_s₁_s₃
    ((isConj_iff.mpr ⟨g, rfl⟩).trans (h.p11.isConj_of_mem_Mbar _ hMb hne))

theorem orbit_s₁_M (h : Hyp fr) {g₀ : G} (hg₀ : g₀ ∈ normalizer (fr.M : Set G))
    (hg₀P : g₀ ∉ normalizer (fr.P₁ : Set G)) :
    {y | ∃ g ∈ normalizer (fr.M : Set G), g * fr.s₁ * g⁻¹ = y} = (fr.M : Set G) \ fr.Mbar := by
  have hs₁M : fr.s₁ ∈ fr.M := h.p10.P₁_le_M h.s₁_mem_P₁
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hg _).mp hs₁M, h.conj_s₁_not_mem_Mbar g⟩
  · rintro ⟨hxM, hxMb⟩
    have htM : fr.t ∈ normalizer (fr.M : Set G) := h.t_mem_normalizer_M
    by_cases hxP : x ∈ fr.P₁
    · have hx1 : x ≠ 1 := fun h1 => hxMb (h1 ▸ one_mem _)
      rw [fr.P₁_eq] at hxP
      rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers fr.orderOf_s₁ hxP with h1 | h1 | h1
      · exact absurd h1 hx1
      · exact ⟨1, one_mem _, by rw [h1]; group⟩
      · exact ⟨fr.t, htM, by rw [h1, h.t_conj_s₁]⟩
    · have hyM : g₀ * fr.s₁ * g₀⁻¹ ∈ fr.M := (Subgroup.mem_normalizer_iff.mp hg₀ _).mp hs₁M
      have hyMb := h.conj_s₁_not_mem_Mbar g₀
      have hyP : g₀ * fr.s₁ * g₀⁻¹ ∉ fr.P₁ := by
        intro hyP
        apply hg₀P
        refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun w hw => ?_
        rw [fr.P₁_eq] at hw hyP ⊢
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [← conj_zpow]
        exact zpow_mem hyP k
      obtain ⟨k, hk, hkx⟩ := h.p11.exists_conj_M _ hyM x hxM hyP hyMb hxP hxMb
      exact ⟨k * g₀, mul_mem (h.normalizer_P₁_le_normalizer_M hk) hg₀, by rw [← hkx]; group⟩

theorem factorization_card_normalizer_M : (162 * (3 ^ 5 * 720) : ℕ).factorization 3 = 11 := by
  rw [show (162 * (3 ^ 5 * 720) : ℕ) = 3 ^ 11 * 160 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem normalizer_M (h : Hyp fr) :
    normalizer (fr.M : Set G) = normalizer (fr.P₁ : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ h.normalizer_P₁_le_normalizer_M
  by_contra hne
  obtain ⟨g₀, hg₀, hg₀P⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  set NM := normalizer (fr.M : Set G)
  have hcard : Nat.card NM = 162 * (3 ^ 5 * 720) := by
    have := card_conj_orbit_mul NM fr.s₁
    have hCle : centralizer ({fr.s₁} : Set G) ≤ NM := by
      rw [← h.centralizer_P₁_eq]
      exact (Subgroup.centralizer_le_normalizer _).trans h.normalizer_P₁_le_normalizer_M
    rw [h.orbit_s₁_M hg₀ hg₀P, Set.ncard_sdiff (fun x hx => h.Mbar_le_M hx) (Set.toFinite _),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe,
      h.p10.card_M, h.card_Mbar, inf_of_le_right hCle, ← h.centralizer_P₁_eq,
      h.card_centralizer_P₁] at this
    rw [← this]
    norm_num
  obtain ⟨B⟩ : Nonempty (Sylow 3 NM) := inferInstance
  have hB : IsSylowOf NM 3 ((B : Subgroup NM).map NM.subtype) := ⟨B, rfl⟩
  set B' := (B : Subgroup NM).map NM.subtype
  have hB'card : Nat.card B' = 3 ^ 11 := by
    rw [card_isSylowOf hB, hcard, factorization_card_normalizer_M]
  have hB'3 : IsPGroup 3 B' := isPGroup_of_isSylowOf hB
  have hMB' : fr.M ≤ B' :=
    le_isSylowOf_of_le_normalizer hB h.isPGroup_M Subgroup.le_normalizer le_rfl
  have hM1 : fr.M ≠ ⊥ := by
    intro hb
    have := h.p10.card_M
    rw [hb, Subgroup.card_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨y, hyM, hy1, hyC⟩ := exists_mem_ne_one_mem_centralizer hB'3 hMB'
    ((le_of_isSylowOf hB).trans le_rfl) hM1
  have hB'C : B' ≤ centralizer ({y} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyC b hb)
  by_cases hyMb : y ∈ fr.Mbar
  · have := h.card_le_of_isConj_s₃ (h.p11.isConj_of_mem_Mbar y hyMb hy1)
      (hB'C.trans (by rw [← centralizer_zpowers]; exact Subgroup.centralizer_le_normalizer _))
      hB'3
    rw [hB'card] at this
    exact absurd this (by norm_num)
  · have hd := Subgroup.card_dvd_of_le hB'C
    rw [hB'card, h.card_centralizer_of_isConj_s₁ (h.isConj_s₁_of_mem_M hyM hyMb)] at hd
    exact absurd (Nat.le_of_dvd (by norm_num) hd) (by norm_num)

theorem U_inf_normalizer_M (h : Hyp fr) : fr.U ⊓ normalizer (fr.M : Set G) = fr.N := by
  rw [h.normalizer_M]
  have hle : fr.N ≤ fr.U ⊓ normalizer (fr.P₁ : Set G) :=
    le_inf h.N_le_U (h.N_le_centralizer_P₁.trans (Subgroup.centralizer_le_normalizer _))
  have hU3 : IsPGroup 3 fr.U := IsPGroup.of_card h.card_U
  exact (Subgroup.eq_of_le_of_card_ge hle
    (card_le_of_isSylowOf h.p11.isSylowOf_N (hU3.to_le inf_le_left) inf_le_right)).symm

theorem I_le_N (h : Hyp fr) : fr.I ≤ fr.N := sup_le h.E_le_N h.ZN_le_N

theorem I_le_U (h : Hyp fr) : fr.I ≤ fr.U := h.I_le_N.trans h.N_le_U

theorem s₂_mem_I (h : Hyp fr) : fr.s₂ ∈ fr.I := (le_sup_left : fr.E ≤ fr.I) h.s₂_mem_E

theorem map_conj_M_ne_I (h : Hyp fr) (k : G) : fr.M.map (MulAut.conj k).toMonoidHom ≠ fr.I := by
  intro hk
  have hmem : fr.s₂ ∈ fr.M.map (MulAut.conj k).toMonoidHom := hk ▸ h.s₂_mem_I
  rw [CFSG.Walter.J1.mem_map_conj] at hmem
  have hw1 : k⁻¹ * fr.s₂ * k ≠ 1 := by
    intro h1
    have := fr.orderOf_s₂
    rw [show fr.s₂ = k * (k⁻¹ * fr.s₂ * k) * k⁻¹ by group, h1, mul_one, mul_inv_cancel,
      orderOf_one] at this
    exact absurd this (by norm_num)
  have hws₂ : IsConj fr.s₂ (k⁻¹ * fr.s₂ * k) := isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]⟩
  by_cases hwM : k⁻¹ * fr.s₂ * k ∈ fr.Mbar
  · exact h.p7.not_isConj_s₂_s₃ (hws₂.trans (h.p11.isConj_of_mem_Mbar _ hwM hw1))
  · exact h.p7.not_isConj_s₁_s₂ (hws₂.trans (h.isConj_s₁_of_mem_M hmem hwM)).symm

theorem U_le_normalizer_I (h : Hyp fr) : fr.U ≤ normalizer (fr.I : Set G) := by
  intro u hu
  set 𝒜 : Set (Subgroup G) :=
    {B | B ≤ fr.N ∧ Nat.card B = 3 ^ 5 ∧ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a}
  have h𝒜 : 𝒜.ncard = 10 := by
    rw [← Nat.card_coe_set_eq]
    exact h.p11.card_abelian
  have hconj : ∀ g ∈ fr.U, ∀ B ∈ 𝒜, B.map (MulAut.conj g).toMonoidHom ∈ 𝒜 := by
    rintro g hg B ⟨hBN, hBc, hBa⟩
    have hgN : g ∈ normalizer (fr.N : Set G) := h.U_le_V hg
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mp (hBN hx)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hBc]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      change g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
      exact conj_mul_comm g (hBa a ha b hb)
  have hM𝒜 : fr.M ∈ 𝒜 := ⟨h.M_le_N, h.p10.card_M, h.p10.M_comm⟩
  have hI𝒜 : fr.I ∈ 𝒜 := ⟨h.I_le_N, h.p11.card_I, h.p11.I_comm⟩
  set O := {D : Subgroup G | ∃ g ∈ fr.U, fr.M.map (MulAut.conj g).toMonoidHom = D}
  have hO : O.ncard = 9 := by
    have := card_conj_subgroup_orbit_mul fr.U fr.M
    rw [h.U_inf_normalizer_M, h.card_U, h.p11.card_N, show (3 : ℕ) ^ 9 = 9 * 3 ^ 7 by norm_num]
      at this
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  have hO𝒜 : O ⊆ 𝒜 := by
    rintro _ ⟨g, hg, rfl⟩
    exact hconj g hg _ hM𝒜
  have hIO : ∀ g ∈ fr.U, fr.I.map (MulAut.conj g).toMonoidHom ∉ O := by
    rintro g hg ⟨k, hk, hkI⟩
    apply h.map_conj_M_ne_I (g⁻¹ * k)
    rw [CFSG.Walter.J1.map_conj_mul, hkI, CFSG.Walter.J1.map_conj_inv_map_conj]
  have hIO' : fr.I ∉ O := by
    have := hIO 1 (one_mem _)
    rwa [CFSG.Walter.J1.map_conj_one] at this
  by_contra hne
  have hIu : fr.I.map (MulAut.conj u).toMonoidHom ≠ fr.I := fun he =>
    hne (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hsub : insert (fr.I.map (MulAut.conj u).toMonoidHom) (insert fr.I O) ⊆ 𝒜 :=
    Set.insert_subset (hconj u hu _ hI𝒜) (Set.insert_subset hI𝒜 hO𝒜)
  have hcard : (insert (fr.I.map (MulAut.conj u).toMonoidHom) (insert fr.I O)).ncard = 11 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem hIO' (Set.toFinite _), hO]
    rintro (h1 | h1)
    · exact hIu h1
    · exact hIO u hu h1
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem z_mem_normalizer_I (h : Hyp fr) : z ∈ normalizer (fr.I : Set G) :=
  h.p11.L_le_normalizer_I h.z_mem_L

theorem centralizer_I (h : Hyp fr) : centralizer (fr.I : Set G) = fr.I := by
  have hle : centralizer (fr.I : Set G) ≤ fr.I ⊔ zpowers z := by
    rw [← h.p11.centralizer_E]
    exact Subgroup.centralizer_le (fun x hx => (le_sup_left : fr.E ≤ fr.I) hx)
  have hIle : fr.I ≤ centralizer (fr.I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => h.p11.I_comm y hy x hx
  have hz2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, h.set.orderOf_z]
  have hzI : zpowers z ⊓ fr.I = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [hz2, h.p11.card_I]; norm_num))
  have hIz : Nat.card (fr.I ⊔ zpowers z : Subgroup G) = 2 * 3 ^ 5 := by
    rw [sup_comm, card_sup_of_inf_eq_bot (Subgroup.zpowers_le.mpr h.z_mem_normalizer_I) hzI, hz2,
      h.p11.card_I]
  have hzC : z ∉ centralizer (fr.I : Set G) := by
    intro hzC
    obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bar (by norm_num)
    have hyS : y ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy
    have hyI : y ∈ fr.I := (le_sup_right : fr.ZN ≤ fr.I) (h.S_le_ZN hyS)
    exact hy1 (h.eq_one_of_mem_Mbar_of_comm_z (h.S_le_Mbar hyS)
      (Subgroup.mem_centralizer_iff.mp hzC y hyI))
  obtain ⟨k, hk⟩ : 3 ^ 5 ∣ Nat.card (centralizer (fr.I : Set G)) :=
    h.p11.card_I ▸ Subgroup.card_dvd_of_le hIle
  have hd : Nat.card (centralizer (fr.I : Set G)) ∣ 2 * 3 ^ 5 := hIz ▸ Subgroup.card_dvd_of_le hle
  rw [hk, mul_comm 2] at hd
  have hk2 : k ∣ 2 := (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge hIle (by rw [hk, mul_one, h.p11.card_I])).symm
  · exfalso
    have heq : centralizer (fr.I : Set G) = fr.I ⊔ zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hIz, hk]; ring_nf; exact le_rfl)
    exact hzC (heq ▸ (le_sup_right : zpowers z ≤ fr.I ⊔ zpowers z) (Subgroup.mem_zpowers z))

theorem centralizer_U (h : Hyp fr) : centralizer (fr.U : Set G) = fr.S := by
  have hle : centralizer (fr.U : Set G) ≤ fr.I := by
    rw [← h.centralizer_I]
    exact Subgroup.centralizer_le fun x hx => h.I_le_U hx
  rw [← h.center_U, inf_eq_right.mpr (hle.trans h.I_le_U)]

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
