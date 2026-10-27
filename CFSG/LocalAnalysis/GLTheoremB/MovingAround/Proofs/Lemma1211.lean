module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1111

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1211

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem isSylowIn_top_gLBConj {G : Type} [Group G] {p : ℕ} {P : Subgroup G}
    (hP : IsSylowIn p ⊤ P) (g : G) : IsSylowIn p ⊤ (GLBConj g P) := by
  refine ⟨le_top, hP.2.1.map (MulAut.conj g⁻¹).toMonoidHom, fun R' _ hR'p hR'le => ?_⟩
  have h1 : P ≤ GLBConj g⁻¹ R' := by
    intro x hx
    rw [mem_gLBConj]
    refine hR'le ?_
    rw [mem_gLBConj]
    have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rw [e]
    exact hx
  have h2 : GLBConj g⁻¹ R' = P :=
    hP.2.2 _ le_top (hR'p.map (MulAut.conj g⁻¹⁻¹).toMonoidHom) h1
  calc R' = GLBConj g (GLBConj g⁻¹ R') := by
          rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]
    _ = GLBConj g P := by rw [h2]

theorem mem_centerOf_iff' {G : Type} [Group G] (H : Subgroup G) (z : G) :
    z ∈ centerOf H ↔ z ∈ H ∧ ∀ h ∈ H, h * z = z * h := by
  unfold centerOf
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨x.2, fun h hh => ?_⟩
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hx) ⟨h, hh⟩)
    simpa using this
  · rintro ⟨hz, hcomm⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2)

section Extraspecial

variable {G : Type} [Group G] [Finite G]

@[expose] def IsExtraspecialThreeFive (F : Subgroup G) : Prop :=
  Nat.card F = 3 ^ 5 ∧ (∀ x ∈ F, x ^ 3 = 1) ∧ ⁅F, F⁆ = centerOf F ∧ Nat.card (centerOf F) = 3

theorem exists_gen_center {F : Subgroup G} (hF : IsExtraspecialThreeFive F) :
    ∃ a : G, a ≠ 1 ∧ centerOf F = Subgroup.zpowers a := by
  obtain ⟨-, hexp, -, hcard⟩ := hF
  have hZF : centerOf F ≤ F := by
    unfold centerOf
    exact Subgroup.map_subtype_le _
  have hnt : ∃ a ∈ centerOf F, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : centerOf F ≤ ⊥ := fun x hx => Subgroup.mem_bot.2 (hall x hx)
    have := Subgroup.card_le_of_le hbot
    rw [hcard, Subgroup.card_bot] at this
    omega
  obtain ⟨a, ha, ha1⟩ := hnt
  have ha3 : a ^ 3 = 1 := hexp a (hZF ha)
  refine ⟨a, ha1, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha)
    (by rw [Lemma1111.card_zpowers_three ha1 ha3]; exact hcard.le)).symm

theorem exists_E27 {F : Subgroup G} (hF : IsExtraspecialThreeFive F) :
    ∃ Ω : Subgroup G, Ω ≤ F ∧ CFSG.Open.IsElemAbelian 3 Ω ∧ Nat.card Ω = 27 ∧ centerOf F ≤ Ω := by
  obtain ⟨a, ha1, hcen⟩ := exists_gen_center hF
  obtain ⟨hcard, hexp, hder, -⟩ := hF
  have hEF : Lemma1111.IsExtraspecialFive F a :=
    ⟨hcard, hexp, ha1, hcen, hder.trans hcen⟩
  have haF : a ∈ F := Lemma1111.zpowers_le_of_ext hEF (Subgroup.mem_zpowers a)
  have ha3 : a ^ 3 = 1 := hexp a haF
  obtain ⟨y, hyF, hy⟩ : ∃ y ∈ F, y ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : F ≤ Subgroup.zpowers a)
    rw [hcard, Lemma1111.card_zpowers_three ha1 ha3] at this
    omega
  have hy3 : y ^ 3 = 1 := hexp y hyF
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hyc : ∀ h ∈ Subgroup.zpowers y, ∀ k ∈ Subgroup.zpowers a, h * k = k * h :=
    fun h hh k hk => Lemma1111.central_of_mem hEF hk ((Subgroup.zpowers_le.2 hyF) hh)
  have hVel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers y ⊔ Subgroup.zpowers a) :=
    Lemma1111.isElemAbelian_sup (Lemma1111.isElemAbelian_zpowers hy3)
      (Lemma1111.isElemAbelian_zpowers ha3) hyc
  have hay : a ∉ Subgroup.zpowers y := by
    intro hay
    apply hy
    rw [Lemma1111.zpowers_eq_of_mem hy3 hy1 hay ha1]
    exact Subgroup.mem_zpowers y
  have hprod1 := Lemma1111.card_sup_mul_card_inf (Subgroup.zpowers y) (Subgroup.zpowers a) hyc
  rw [Lemma1111.inf_zpowers_trivial ha3 ha1 hay, Lemma1111.card_zpowers_of_ne_one hy3
    (Subgroup.mem_zpowers y) hy1, Lemma1111.card_zpowers_three ha1 ha3] at hprod1
  have hVcard : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers a) = 9 := by omega
  have hC81 : Nat.card ↥(F ⊓ Subgroup.centralizer ({y} : Set G)) = 81 :=
    Lemma1111.card_centralizer_inf hEF hyF hy
  obtain ⟨y', hy'C, hy'V⟩ : ∃ y' ∈ F ⊓ Subgroup.centralizer ({y} : Set G),
      y' ∉ Subgroup.zpowers y ⊔ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le
      (fun x hx => hall x hx : F ⊓ Subgroup.centralizer ({y} : Set G) ≤
        Subgroup.zpowers y ⊔ Subgroup.zpowers a)
    omega
  obtain ⟨hy'F, hy'cent⟩ := Subgroup.mem_inf.1 hy'C
  have hyy' : y * y' = y' * y := (Subgroup.mem_centralizer_iff.1 hy'cent) y (Set.mem_singleton y)
  have hy'3 : y' ^ 3 = 1 := hexp y' hy'F
  have hy'1 : y' ≠ 1 := fun h => hy'V (h ▸ Subgroup.one_mem _)
  have hyC' : y ∈ Subgroup.centralizer ({y'} : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hyy'.symm)
  have haC' : a ∈ Subgroup.centralizer ({y'} : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Lemma1111.central_of_mem hEF (Subgroup.mem_zpowers a) hy'F)
  have hVc : Subgroup.zpowers y ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({y'} : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hyC') (Subgroup.zpowers_le.2 haC')
  have hc' : ∀ h ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers a, ∀ k ∈ Subgroup.zpowers y',
      h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hcomm : Commute h y' := (Subgroup.mem_centralizer_iff.1 (hVc hh) y' (Set.mem_singleton y')).symm
    exact (hcomm.zpow_right m).eq
  have hinf2 := Lemma1111.inf_zpowers_trivial hy'3 hy'1 hy'V
  have hprod2 := Lemma1111.card_sup_mul_card_inf (Subgroup.zpowers y ⊔ Subgroup.zpowers a)
    (Subgroup.zpowers y') hc'
  rw [hinf2, hVcard, Lemma1111.card_zpowers_of_ne_one hy'3 (Subgroup.mem_zpowers y') hy'1] at hprod2
  refine ⟨Subgroup.zpowers y ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers y', ?_, ?_, ?_, ?_⟩
  · exact sup_le (sup_le (Subgroup.zpowers_le.2 hyF) (Lemma1111.zpowers_le_of_ext hEF))
      (Subgroup.zpowers_le.2 hy'F)
  · exact Lemma1111.isElemAbelian_sup hVel (Lemma1111.isElemAbelian_zpowers hy'3) hc'
  · omega
  · rw [hcen]
    exact (le_sup_right : Subgroup.zpowers a ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers a).trans le_sup_left

end Extraspecial

section Inputs

@[expose] def Input31_2_three : Prop :=
  ∀ (G : Type) [Group G] (R Q : Subgroup G), IsPGroup 3 ↥R → Q ≤ R → (Q.subgroupOf R).Normal →
    IsExtraspecialThreeFive Q → ⁅R, Q⁆ ≤ centerOf Q → R ≤ Q ⊔ Subgroup.centralizer (Q : Set G)

@[expose] def Input_cyc3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPGroup 3 X →
    (∀ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3) → IsCyclic X

@[expose] def Input24_5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.Open.IsKGroup X → p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → Subgroup.center X ≠ ⊥ → 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ P : Subgroup X, IsSylowIn p ⊤ P → IsCyclic ↥(centerOf P) →
      CFSG.ABGLocalTools.IsPConstrained p X ∨
        (⊤ : Subgroup X) = GLBCore p 4 P ⊔ ⨆ (E : Subgroup X) (_ : IsEkIn p 4 P E), GLBCore p 2 E

@[expose] def IsSL2Nine (X : Type) [Group X] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 9 ∧ Nonempty (X ≃* ↥(StatedSL 2 F))

end Inputs

section Structure

variable {G : Type} [Group G] [Finite G]

@[expose] def TI3 (C O : Subgroup G) : Prop :=
  ∀ S T : Subgroup G, IsSylowIn 3 C S → IsSylowIn 3 C T → S ⊔ O ≠ T ⊔ O →
    (S ⊔ O) ⊓ (T ⊔ O) ≤ O

theorem isElemAbelian_map_val {C : Subgroup G} {E : Subgroup ↥C}
    (hE : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.map C.subtype) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb'eq⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    rw [← ha'eq, ← hb'eq, ← MonoidHom.map_mul, ← MonoidHom.map_mul]
    exact congrArg C.subtype (congrArg Subtype.val (hE.1.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩))
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← MonoidHom.map_pow, hE.2 x' hx', map_one]

theorem mem_of_pow_three_of_cyclic {C Z : Subgroup G} [IsCyclic ↥C] (hZC : Z ≤ C)
    (hZ : Nat.card Z = 3) {c : G} (hcC : c ∈ C) (hc3 : c ^ 3 = 1) : c ∈ Z := by
  by_cases hc1 : c = 1
  · rw [hc1]; exact Z.one_mem
  have hcZ : Nat.card (Subgroup.zpowers (⟨c, hcC⟩ : ↥C)) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext hc3
    · intro h
      apply hc1
      exact congrArg Subtype.val h
  have hZ' : Nat.card (Z.subgroupOf C) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZ]
  have heq : Subgroup.zpowers (⟨c, hcC⟩ : ↥C) = Z.subgroupOf C :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [hcZ, hZ'])
  have hmem : (⟨c, hcC⟩ : ↥C) ∈ Z.subgroupOf C := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem R1_structure (hI : Input31_2_three) (hcyc : Input_cyc3)
    {R₁ R₃ : Subgroup G} (hR₁ : IsPGroup 3 ↥R₁) (hR₃ : R₃ ≤ R₁) (hn : (R₃.subgroupOf R₁).Normal)
    (hext : IsExtraspecialThreeFive R₃) (hcomm : ⁅R₁, R₃⁆ ≤ centerOf R₃)
    (hm3 : ∀ E : Subgroup G, E ≤ R₁ → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) :
    IsCyclic ↥(centerOf R₁) ∧ R₁ = centerOf R₁ ⊔ omegaOne 3 R₁ ∧ Nat.card ↥(omegaOne 3 R₁) = 3 ^ 5 ∧
      ⁅omegaOne 3 R₁, omegaOne 3 R₁⁆ = centerOf (omegaOne 3 R₁) ∧
        Nat.card ↥(centerOf (omegaOne 3 R₁)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := R₁ ⊓ Subgroup.centralizer (R₃ : Set G) with hCdef
  have hC_le : C ≤ R₁ := inf_le_left
  have hCcent : ∀ c ∈ C, ∀ r ∈ R₃, r * c = c * r := fun c hc r hr =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) r hr
  have hsup' : R₁ ≤ R₃ ⊔ Subgroup.centralizer (R₃ : Set G) :=
    hI G R₁ R₃ hR₁ hR₃ hn hext hcomm
  have hsup : R₁ = R₃ ⊔ C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨s, hs, k, hk, rfl⟩ := Lemma1111.mem_sup_prod
        (fun h hh k hk => (Subgroup.mem_centralizer_iff.1 hk) h hh) (hsup' hx)
      have hkR1 : k ∈ R₁ := by
        have e : k = s⁻¹ * (s * k) := by group
        rw [e]
        exact R₁.mul_mem (R₁.inv_mem (hR₃ hs)) hx
      exact (R₃ ⊔ C).mul_mem (Subgroup.mem_sup_left hs)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hkR1, hk⟩))
    · exact sup_le hR₃ hC_le
  have hZC : centerOf R₃ ≤ C := by
    intro z hz
    obtain ⟨hzR3, hzc⟩ := (mem_centerOf_iff' R₃ z).1 hz
    exact Subgroup.mem_inf.2 ⟨hR₃ hzR3, Subgroup.mem_centralizer_iff.2 (fun h hh => hzc h hh)⟩
  have hCE : ∀ E : Subgroup G, E ≤ C → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 := by
    intro E hEC hE
    by_contra hgt
    push Not at hgt
    obtain ⟨Ω, hΩF, hΩel, hΩcard, -⟩ := exists_E27 hext
    have hcEΩ : ∀ e ∈ E, ∀ w ∈ Ω, e * w = w * e := fun e he w hw =>
      (hCcent e (hEC he) w (hΩF hw)).symm
    have hEΩel : CFSG.Open.IsElemAbelian 3 (E ⊔ Ω) :=
      Lemma1111.isElemAbelian_sup hE hΩel (fun h hh k hk => hcEΩ h hh k hk)
    have hEΩR : E ⊔ Ω ≤ R₁ := sup_le (hEC.trans hC_le) (hΩF.trans hR₃)
    have hmE := hm3 (E ⊔ Ω) hEΩR hEΩel
    have hinter : E ⊓ Ω ≤ centerOf R₃ := by
      intro x hx
      obtain ⟨hxE, hxΩ⟩ := Subgroup.mem_inf.1 hx
      rw [mem_centerOf_iff']
      exact ⟨hΩF hxΩ, fun h hh => (hCcent x (hEC hxE) h hh)⟩
    have hcardI : Nat.card ↥(E ⊓ Ω) ≤ 3 := by
      have := Subgroup.card_le_of_le hinter
      rw [hext.2.2.2] at this
      exact this
    have hprod := Lemma1111.card_sup_mul_card_inf E Ω (fun h hh k hk => hcEΩ h hh k hk)
    rw [hΩcard] at hprod
    have hEp : IsPGroup 3 ↥E := Lemma1111.isPGroup_of_elemAbelian hE
    obtain ⟨k, hk⟩ := exists_card_eq_pow hEp
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> omega
    have h9 : 9 ≤ Nat.card ↥E := by
      rw [hk]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hXY : Nat.card ↥(E ⊔ Ω) * Nat.card ↥(E ⊓ Ω) ≤ 27 * 3 :=
      Nat.mul_le_mul hmE hcardI
    omega
  have hCcyc : IsCyclic ↥C := by
    apply hcyc ↥C
    · intro g
      obtain ⟨n, hn⟩ := hR₁ ⟨g.1, hC_le g.2⟩
      refine ⟨n, Subtype.ext ?_⟩
      simpa using congrArg Subtype.val hn
    · intro E' hE'
      have hmap := isElemAbelian_map_val hE'
      have := hCE (E'.map C.subtype) (Subgroup.map_subtype_le _) hmap
      rwa [Subgroup.card_map_of_injective (f := C.subtype) Subtype.coe_injective] at this
  haveI := hCcyc
  have hCcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥C) ⟨y, hy⟩)
  have hZ1 : centerOf R₁ = C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxR1, hxc⟩ := (mem_centerOf_iff' R₁ x).1 hx
      exact Subgroup.mem_inf.2 ⟨hxR1, Subgroup.mem_centralizer_iff.2 (fun h hh => hxc h (hR₃ hh))⟩
    · intro c hc
      rw [mem_centerOf_iff']
      refine ⟨hC_le hc, fun h hh => ?_⟩
      have hcen : R₃ ⊔ C ≤ Subgroup.centralizer ({c} : Set G) := by
        refine sup_le (fun r hr => ?_) (fun c' hc' => ?_)
        · exact Subgroup.mem_centralizer_iff.2 (fun g hg => by
            rw [Set.mem_singleton_iff] at hg
            rw [hg]
            exact (hCcent c hc r hr).symm)
        · exact Subgroup.mem_centralizer_iff.2 (fun g hg => by
            rw [Set.mem_singleton_iff] at hg
            rw [hg]
            exact hCcomm c hc c' hc')
      rw [hsup] at hh
      exact (Subgroup.mem_centralizer_iff.1 (hcen hh) c (Set.mem_singleton c)).symm
  have hΩ : omegaOne 3 R₁ = R₃ := by
    apply le_antisymm
    · unfold omegaOne
      apply (Subgroup.closure_le R₃).2
      rintro x ⟨hxR1, hx3⟩
      rw [hsup] at hxR1
      obtain ⟨s, hs, c, hc, rfl⟩ := Lemma1111.mem_sup_prod (fun h hh k hk => hCcent k hk h hh) hxR1
      have hsc : Commute s c := hCcent c hc s hs
      have hpow : s ^ 3 * c ^ 3 = 1 := by
        rw [← hsc.mul_pow]
        exact hx3
      rw [hext.2.1 s hs, one_mul] at hpow
      have hcZ : c ∈ centerOf R₃ := mem_of_pow_three_of_cyclic hZC hext.2.2.2 hc hpow
      exact R₃.mul_mem hs ((mem_centerOf_iff' R₃ c).1 hcZ).1
    · intro s hs
      exact Subgroup.subset_closure ⟨hR₃ hs, hext.2.1 s hs⟩
  rw [hZ1, hΩ]
  exact ⟨hCcyc, hsup.trans (sup_comm _ _), hext.1, hext.2.2.1, hext.2.2.2⟩

theorem le_inf_of_TI3 {C O M R R' A : Subgroup G} (hTI : TI3 C O) (hOM : O ≤ M) (hRM : R ≤ M)
    (hR : IsSylowIn 3 C R) (hR' : IsSylowIn 3 C R') (hR'M : ¬ R' ≤ M) (hAR : A ≤ R) (hAR' : A ≤ R') :
    A ≤ R ⊓ O := by
  have hne : R ⊔ O ≠ R' ⊔ O := by
    intro heq
    apply hR'M
    calc R' ≤ R' ⊔ O := le_sup_left
      _ = R ⊔ O := heq.symm
      _ ≤ M := sup_le hRM hOM
  have hA : A ≤ (R ⊔ O) ⊓ (R' ⊔ O) :=
    le_inf (le_sup_of_le_left hAR) (le_sup_of_le_left hAR')
  exact le_inf hAR (le_trans hA (hTI R R' hR hR' hne))

end Structure

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn_above' {p : ℕ} [Fact p.Prime] {X P : Subgroup G} (hPX : P ≤ X)
    (hP : IsPGroup p ↥P) : ∃ Q : Subgroup G, IsSylowIn p X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩

theorem isPGroup_of_le' {p : ℕ} {P H : Subgroup G} (hP : IsPGroup p ↥P) (hHP : H ≤ P) :
    IsPGroup p ↥H := fun g => by
  obtain ⟨n, hn⟩ := hP ⟨g.1, hHP g.2⟩
  exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩

end Helpers

section Assembly

@[expose] def AlphaData1211 {G : Type} [Group G] [Finite G] (p : ℕ) (M E A N K : Subgroup G) : Prop :=
  Lemma129Common p M E A N K ∧ (p = 3 ∧ 5 ≤ CFSG.Open.pRank 3 E ∧ IsAltType 13 (barOf 3 K) ∧
    barX 3 N A ≤ barX 3 N K ∧ Lemma129IvAData N K E A)

@[expose] def Claim1211_alpha : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
    (h : Cex127 G m p B M E A N D), ∃ K : Subgroup G, AlphaData1211 p M E A N K

@[expose] def Claim1211_R3 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M) {R : Subgroup G} (hR : IsSylowIn 3 (Cg z) R)
    (hAR : A ≤ R) (hRM : R ≤ M),
    ∃ R₃ : Subgroup G, R₃ ≤ R ⊓ pPrimePCore 3 (Cg z) ∧
      (R₃.subgroupOf (R ⊓ pPrimePCore 3 (Cg z))).Normal ∧ IsExtraspecialThreeFive R₃ ∧
      ⁅R ⊓ pPrimePCore 3 (Cg z), R₃⁆ ≤ centerOf R₃

@[expose] def Claim1211_m3 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M) {R : Subgroup G} (hR : IsSylowIn 3 (Cg z) R)
    (hAR : A ≤ R) (hRM : R ≤ M),
    ∀ E' : Subgroup G, E' ≤ R ⊓ pPrimePCore 3 (Cg z) → CFSG.Open.IsElemAbelian 3 E' →
      Nat.card E' ≤ 3 ^ 3

@[expose] def Claim1211_TI : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
    TI3 (Cg z) (pPrimePCore 3 (Cg z))

@[expose] def Claim1211_OM : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
    pPrimePCore 3 (Cg z) ≤ M

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1211

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1211

theorem lemma1211_i_of_lemma129 (h129 : Lemma129PrintedStatement) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {z : G} (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z),
      ∃ R : Subgroup G, IsSylowIn p (Cg z) R ∧ A ≤ R ∧ R ≤ M := by
  intro G _ _ m p B M E A N D h z hz hz1
  obtain ⟨K, hK, -⟩ := h129 h
  have hE2 : CFSG.Open.pRank p (E ⊓ A) = 2 := hK.2.1.2
  have hEA := h.pair
  have hAM : A ≤ M := hEA.1.2.1.1.1.1
  have hAel : CFSG.Open.IsElemAbelian p A := hEA.1.2.1.1.1.2.1
  haveI : Fact p.Prime := ⟨h.standing.prime⟩
  obtain ⟨R0, hR0M, hzR0⟩ := hz1
  have hR0G : IsSylowIn p ⊤ R0 :=
    (lemma104_iv_holds h.toSec11.toSec10Fails hEA hE2 hR0M).2.2
  have hzA : z ∈ A := hz.1
  have hAC : A ≤ Cg z := by
    intro a ha
    rw [Cg, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨z, hzA⟩ ⟨a, ha⟩)
  have hR0C : R0 ≤ Cg z := by
    intro r hr
    rw [Cg, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact ((mem_centerOf_iff' R0 z).1 hzR0).2 r hr |>.symm
  have hAK : A ≤ Cg z ⊓ M := fun a ha => ⟨hAC ha, hAM ha⟩
  have hR0K : R0 ≤ Cg z ⊓ M := fun r hr => ⟨hR0C hr, hR0M.1 hr⟩
  have hAp : IsPGroup p ↥A := fun g => ⟨1, Subtype.ext (by simpa using hAel.2 g.1 g.2)⟩
  obtain ⟨x, -, S, hSp, hSK, hAS, hconjS⟩ :=
    exists_conj_le_pGroup' (p := p) hAK hAp hR0K hR0M.2.1
  have hSeq : S = GLBConj x R0 := (isSylowIn_top_gLBConj hR0G x).2.2 S le_top hSp hconjS
  have hS_top : IsSylowIn p ⊤ S := by
    rw [hSeq]
    exact isSylowIn_top_gLBConj hR0G x
  refine ⟨S, ⟨hSK.trans inf_le_left, hSp, fun R' _ hR'p hSR' => hS_top.2.2 R' le_top hR'p hSR'⟩,
    hAS, hSK.trans inf_le_right⟩

theorem lemma1211_iii_iv_of_inputs (hI : Input31_2_three) (hcyc : Input_cyc3)
    (h1210 : Lemma1210Statement) (hR3 : Claim1211_R3) (hm3 : Claim1211_m3) (hTI : Claim1211_TI)
    (hOM : Claim1211_OM) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : AlphaData1211 p M E A N K)
      {z : G} (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M)
      (R : Subgroup G), IsSylowIn 3 (Cg z) R → A ≤ R → R ≤ M →
        let R₁ := R ⊓ pPrimePCore 3 (Cg z)
        (IsCyclic (centerOf R₁) ∧ R₁ = centerOf R₁ ⊔ omegaOne 3 R₁ ∧
          Nat.card (omegaOne 3 R₁) = 3 ^ 5 ∧ ⁅omegaOne 3 R₁, omegaOne 3 R₁⁆ = centerOf (omegaOne 3 R₁) ∧
            Nat.card (centerOf (omegaOne 3 R₁)) = 3) ∧ A ≤ R₁ := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2 R hR hAR hRM
  intro R₁
  have hR₁ : IsPGroup 3 ↥R₁ := isPGroup_of_le' hR.2.1 inf_le_left
  obtain ⟨R₃, hR₃R₁, hn, hext, hcomm⟩ := hR3 h hK hz hz1 hz2 hR hAR hRM
  have hm3' := hm3 h hK hz hz1 hz2 hR hAR hRM
  have hiii := R1_structure hI hcyc hR₁ hR₃R₁ hn hext hcomm hm3'
  refine ⟨hiii, ?_⟩
  obtain ⟨φ, hOrb, F, a, hF⟩ := hK.2.2.2.2.2
  obtain ⟨-, -, -, -, -, hQ, -⟩ := h1210 h hK.1
    ⟨hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2.1⟩ φ hOrb hF
  obtain ⟨Q, hQN, hzQ, hAQ, hQM⟩ := hQ z hz.1 hz.2
  have hQC : Q ≤ Cg z := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 (fun g hg => ?_)
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (((mem_centerOf_iff' Q z).1 hzQ).2 x hx).symm
  obtain ⟨R', hR'C, hQR'⟩ := exists_isSylowIn_above' hQC hQN.2.1
  exact le_inf_of_TI3 (hTI h hK hz hz1 hz2) (hOM h hK hz hz1 hz2) hRM hR hR'C
    (fun hR'M => hQM (hQR'.trans hR'M)) hAR (hAQ.trans hQR')

theorem lemma1211_p_eq_three_of_alpha (hα : Claim1211_alpha) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {z : G} (_ : z ∈ A ∧ z ≠ 1) (_ : IsPCentralIn p M z)
      (_ : ¬ Cg z ≤ M), p = 3 := by
  intro G _ _ m p B M E A N D h z _ _ _
  obtain ⟨K, hK⟩ := hα h
  exact hK.2.1

theorem lemma1211_of_inputs (hI : Input31_2_three) (hcyc : Input_cyc3)
    (h129 : Lemma129PrintedStatement) (h1210 : Lemma1210Statement)
    (hα : Claim1211_alpha) (hR3 : Claim1211_R3)
    (hm3 : Claim1211_m3) (hTI : Claim1211_TI) (hOM : Claim1211_OM) :
    Lemma1211Statement := by
  intro G _ _ m p B M E A N D h z hz hz1 hz2
  refine ⟨lemma1211_i_of_lemma129 h129 h hz hz1,
    lemma1211_p_eq_three_of_alpha hα h hz hz1 hz2, ?_⟩
  intro R hR hAR hRM
  obtain ⟨K, hK⟩ := hα h
  exact lemma1211_iii_iv_of_inputs hI hcyc h1210 hR3 hm3 hTI hOM h hK hz hz1 hz2 R hR hAR hRM

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
