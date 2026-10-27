module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.RowL3E8E
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf12L3E8
public import CFSG.ClassicalInvolution.Q3.TL3T25

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
open scoped Matrix

theorem l3Two_card' : Nat.card L3Two = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def slEquivGL' : L3Two ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : L3Two →* GL (Fin 3) (ZMod 2))
    (Matrix.SpecialLinearGroup.toGL_injective.bijective_of_nat_card_le (by
      rw [l3Two_card', CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 3]
      simp [Fin.prod_univ_succ]))

variable {G : Type} [Group G] [Finite G]

theorem exists_action_e8 (E : Subgroup G) [E.Normal] (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ x ∈ E, x * x = 1) (h8 : Nat.card E = 8) :
    ∃ Θ : G →* L3Two, ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (E : Set G) := by
  have hcomm' : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hpow : ∀ a : E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa [sq] using hsq a a.2)
  obtain ⟨ε⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm' hpow
    (n := 3) (by rw [h8]; norm_num)
  let Θ : G →* L3Two := slEquivGL'.symm.toMonoidHom.comp
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL ε).toMonoidHom.comp MulAut.conjNormal)
  refine ⟨Θ, fun x => ?_⟩
  have hΘ : Θ x = 1 ↔ MulAut.conjNormal x = (1 : MulAut E) := by
    constructor
    · intro hx
      apply (CFSG.SectionRank.Ccomm.elemAutEquivGL ε).injective
      have h1 : slEquivGL' (Θ x) = CFSG.SectionRank.Ccomm.elemAutEquivGL ε (MulAut.conjNormal x) :=
        slEquivGL'.apply_symm_apply _
      rw [← h1, hx, map_one, map_one]
    · intro hx
      apply slEquivGL'.injective
      have h1 : slEquivGL' (Θ x) = CFSG.SectionRank.Ccomm.elemAutEquivGL ε (MulAut.conjNormal x) :=
        slEquivGL'.apply_symm_apply _
      rw [h1, hx, map_one, map_one]
  rw [hΘ]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h3 : ((MulAut.conjNormal x ⟨y, hy⟩ : E) : G) = y := by rw [hx]; rfl
    rw [MulAut.conjNormal_apply] at h3
    change x * y * x⁻¹ = y at h3
    calc y * x = (x * y * x⁻¹) * x := by rw [h3]
      _ = x * y := by group
  · intro hx
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    change x * (w : G) * x⁻¹ = (w : G)
    rw [← Subgroup.mem_centralizer_iff.mp hx w w.2]
    group

namespace Std

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {z j : G} (h : Std Ω K J z j)
include h

variable {K' : Subgroup G} {u v s : G}

theorem comm_mem_eGrp (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {M : Subgroup G} (hM : M ∈ Ω) {x a : G}
    (hx : x ∈ M) (ha : a ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) :
    x * a * x⁻¹ * a⁻¹ ∈ eGrp Ω z K := by
  have h8 := h.card_eGrp_K d hs
  haveI := h.eGrp_normal h8
  set E := eGrp Ω z K with hE
  set A := Subgroup.centralizer (E : Set G) with hA
  haveI hAn : A.Normal := inferInstance
  obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution h.hΩ.hyp hM
  obtain ⟨gm, hgm⟩ := h.exists_conj hM hm
  have hmE : m ∈ E := hgm ▸ h.conj_mem_eGrp h8 gm
  have hMa : conjSub a M ∈ twinSet Ω M := by
    refine ⟨h.hΩ.hyp.conjInvariant a M hM, m, hm, ?_⟩
    have h1 := hm.conj a
    rwa [show a * m * a⁻¹ = m by rw [← Subgroup.mem_centralizer_iff.mp ha m hmE]; group] at h1
  have hc1 : x * a * x⁻¹ * a⁻¹ ∈ M ⊔ conjSub a M := by
    rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
      (Subgroup.mem_sup_right (conj_mem_conjSub (M.inv_mem hx)))
  have hc2 : x * a * x⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem (hAn.conj_mem a ha x) (A.inv_mem ha)
  obtain ⟨g, hg⟩ := h.exists_conjSub hM
  have hle : ∀ L ∈ twinSet Ω K, L ≤ pairNormalizers K J z j := by
    intro L hL
    rw [d.tor.htw] at hL
    rcases hL with rfl | rfl
    · exact d.K_le_Y
    · exact d.K'_le_Y
  have hMa' : conjSub g⁻¹ (conjSub a M) ∈ twinSet Ω K := by
    have h1 : conjSub g⁻¹ (conjSub a M) ∈ twinSet Ω (conjSub g⁻¹ M) := by
      rw [twinSet_conjSub h.hΩ.hyp.conjInvariant]
      exact ⟨_, hMa, rfl⟩
    rwa [twinSet_eq_twinSet_of_mem hg] at h1
  have hc3 : g⁻¹ * (x * a * x⁻¹ * a⁻¹) * g⁻¹⁻¹ ∈ pairNormalizers K J z j := by
    have h1 := conj_mem_conjSub (n := g⁻¹) hc1
    rw [Sec7.conjSub_sup_eq] at h1
    exact sup_le (hle _ hg) (hle _ hMa') h1
  have hc4 : g⁻¹ * (x * a * x⁻¹ * a⁻¹) * g⁻¹⁻¹ ∈ A := hAn.conj_mem _ hc2 g⁻¹
  have hc5 := h.le_eGrp_of_centralizer d hs ⟨hc3, hc4⟩
  have h6 := (inferInstance : E.Normal).conj_mem _ hc5 g
  simpa [mul_assoc] using h6

theorem comm_mem_eGrp' (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) (g : G) {a : G}
    (ha : a ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) :
    g * a * g⁻¹ * a⁻¹ ∈ eGrp Ω z K := by
  have h8 := h.card_eGrp_K d hs
  haveI := h.eGrp_normal h8
  set E := eGrp Ω z K with hE
  set A := Subgroup.centralizer (E : Set G) with hA
  set π := QuotientGroup.mk' E with hπ
  set C := (Subgroup.centralizer ((A.map π : Subgroup (G ⧸ E)) : Set (G ⧸ E))).comap π with hC
  have hmem : ∀ x : G, (∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ E) → x ∈ C := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : π (x * b * x⁻¹ * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr (hx b hb)
    simp only [map_mul, map_inv] at h1
    have h2 : π x * π b = π b * π x := by
      calc π x * π b = (π x * π b * (π x)⁻¹ * (π b)⁻¹) * (π b * π x) := by group
        _ = π b * π x := by rw [h1, one_mul]
    exact h2.symm
  have hle : ∀ M ∈ Ω, M ≤ C := fun M hM x hx => hmem x fun b hb => h.comm_mem_eGrp d hs hM hx hb
  have htop : (⊤ : Subgroup G) ≤ C := by
    rw [← h.hgen]
    exact iSup₂_le hle
  have hgC := htop (Subgroup.mem_top g)
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hgC
  have h1 := hgC (π a) ⟨a, ha, rfl⟩
  have h2 : π (g * a * g⁻¹ * a⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← h1]
    group
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem isPGroup_centralizer (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) :
    IsPGroup 2 ↥(Subgroup.centralizer (eGrp Ω z K : Set G)) := by
  set E := eGrp Ω z K with hE
  set A := Subgroup.centralizer (E : Set G) with hA
  have hodd : ∀ a ∈ A, Odd (orderOf a) → a = 1 := by
    intro a ha hao
    have hcen : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have he := h.comm_mem_eGrp' d hs g ha
      set e := g * a * g⁻¹ * a⁻¹ with he_def
      have hga : g * a * g⁻¹ = e * a := by rw [he_def]; group
      have hea : Commute e a := Subgroup.mem_centralizer_iff.mp ha e he
      have hee : e * e = 1 := h.eGrp_sq K e he
      obtain ⟨k, hk⟩ := hao
      have h1 : (g * a * g⁻¹) ^ orderOf a = 1 := by
        rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      rw [hga, hea.mul_pow, pow_orderOf_eq_one, mul_one, hk, pow_succ, pow_mul, sq, hee,
        one_pow, one_mul] at h1
      rw [he_def] at h1
      calc g * a = (g * a * g⁻¹ * a⁻¹) * (a * g) := by group
        _ = a * g := by rw [h1, one_mul]
    have h2 := (TC.Thin.isPGroup_center_of_oddCore h.hO) ⟨a, hcen⟩
    obtain ⟨k, hk⟩ := h2
    have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases i with _ | i
    · exact orderOf_eq_one_iff.mp (by simpa using hi)
    · exfalso
      rw [hi] at hao
      exact (Nat.not_even_iff_odd.mpr hao) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  intro x
  have h1 := Sec7.odd_orderOf_pow_four_pow (x : G)
  have h2 := hodd _ (A.pow_mem x.2 _) h1
  refine ⟨2 * orderOf (x : G), Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  exact h2

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
