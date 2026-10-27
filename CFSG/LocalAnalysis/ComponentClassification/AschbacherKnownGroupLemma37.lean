module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Shapes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Burnside
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Gap
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

theorem setup [Finite G] {A C : Subgroup G} {t : G} (hC : C = A ⊓ centralizer ({t} : Set G))
    (htN : t ∈ normalizer (A : Set G)) (ht2 : t ^ 2 = 1) (R : Sylow 2 C)
    (hRcyc : IsCyclic (R : Subgroup C)) (hRcard : Nat.card R = 4) :
    ∃ (S₀ : Sylow 2 A) (x : G), x ∈ (S₀ : Subgroup A).map A.subtype ∧ orderOf x = 4 ∧
      x * t = t * x ∧
      t ∈ normalizer (((S₀ : Subgroup A).map A.subtype : Subgroup G) : Set G) ∧
      (∀ s ∈ (S₀ : Subgroup A).map A.subtype, s * t = t * s → s ∈ zpowers x) ∧
      (t ∈ A → t ∈ zpowers x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCmem : ∀ g : G, g ∈ C ↔ g ∈ A ∧ g * t = t * g := by
    intro g
    rw [hC, mem_inf, mem_centralizer_singleton_iff]
  obtain ⟨g₀, hg₀⟩ := hRcyc.exists_generator
  set x : G := ((g₀ : C) : G) with hx
  have hxo : orderOf x = 4 := by
    rw [hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₀]
    exact hRcard
  have hxC : x ∈ C := (g₀ : C).2
  have hxA : x ∈ A := ((hCmem x).1 hxC).1
  have hxt : x * t = t * x := ((hCmem x).1 hxC).2
  have hRx : ∀ r ∈ (R : Subgroup C).map C.subtype, r ∈ zpowers x := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg₀ ⟨c, hc⟩)
    have : c = (g₀ : C) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [this]
    exact ⟨k, by simp [hx]⟩
  have hxR : x ∈ (R : Subgroup C).map C.subtype := ⟨g₀, g₀.2, rfl⟩
  have hxp : IsPGroup 2 (zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hxo]
    exact ⟨2, by norm_num⟩
  have htp : IsPGroup 2 (zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact ht2) : orderOf t ∣ 2 ^ 1)
    exact ⟨i, hi⟩
  have hQp : IsPGroup 2 (zpowers x ⊔ zpowers t : Subgroup G) := by
    refine hxp.to_sup_of_normal_left' htp (zpowers_le.2 ?_)
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact (Commute.zpow_left hxt k).eq
  have hQN : zpowers x ⊔ zpowers t ≤ normalizer (A : Set G) :=
    sup_le (zpowers_le.2 (le_normalizer hxA)) (zpowers_le.2 htN)
  obtain ⟨S₀, hS₀⟩ :=
    LocalAnalysis.ComponentInitial.TwoGroupAction.exists_sylow_le_normalizer hQp hQN
  set S := (S₀ : Subgroup A).map A.subtype with hS
  have hmemS : ∀ h : A, (h : G) ∈ S ↔ h ∈ (S₀ : Subgroup A) := by
    intro h
    constructor
    · rintro ⟨h', hh', hh'h⟩
      rwa [← Subtype.ext hh'h]
    · intro hh
      exact ⟨h, hh, rfl⟩
  have htNS : t ∈ normalizer (S : Set G) := hS₀ (mem_sup_right (mem_zpowers t))
  have hxNS : x ∈ normalizer (S : Set G) := hS₀ (mem_sup_left (mem_zpowers x))
  have hxS : x ∈ S := by
    set x' : A := ⟨x, hxA⟩
    have hx'N : x' ∈ normalizer ((S₀ : Subgroup A) : Set A) := by
      rw [mem_normalizer_iff]
      intro h
      rw [← hmemS, ← hmemS]
      exact mem_normalizer_iff.1 hxNS h
    have hx'p : IsPGroup 2 (zpowers x') := by
      rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk, hxo]
      exact ⟨2, by norm_num⟩
    have hQ := S₀.isPGroup'.to_sup_of_normal_left' hx'p (zpowers_le.2 hx'N)
    have heq : (S₀ : Subgroup A) ⊔ zpowers x' = S₀ := S₀.is_maximal' hQ le_sup_left
    have : x' ∈ (S₀ : Subgroup A) := by
      rw [← heq]
      exact mem_sup_right (mem_zpowers x')
    exact (hmemS x').2 this
  have hcent : ∀ s ∈ S, s * t = t * s → s ∈ zpowers x := by
    intro s hs hst
    set X := S ⊓ centralizer ({t} : Set G) with hX
    have hXp : IsPGroup 2 X := (S₀.isPGroup'.map A.subtype).to_le inf_le_left
    have hXC : X ≤ C := fun g hg => (hCmem g).2
      ⟨map_subtype_le _ (mem_inf.1 hg).1, mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2⟩
    have hRX : (R : Subgroup C).map C.subtype ≤ X := by
      intro r hr
      have hrx := hRx r hr
      refine mem_inf.2 ⟨zpowers_le.2 hxS hrx, ?_⟩
      obtain ⟨c, -, rfl⟩ := hr
      exact mem_centralizer_singleton_iff.2 ((hCmem c).1 c.2).2
    have heq := LocalAnalysis.ComponentInitial.TwoGroupAction.sylow_map_eq_of_le R hXp hXC hRX
    have hsX : s ∈ X := mem_inf.2 ⟨hs, mem_centralizer_singleton_iff.2 hst⟩
    rw [heq] at hsX
    exact hRx s hsX
  refine ⟨S₀, x, hxS, hxo, hxt, htNS, hcent, fun htA => ?_⟩
  have htC : t ∈ C := (hCmem t).2 ⟨htA, rfl⟩
  set t' : C := ⟨t, htC⟩
  have ht'n : (zpowers t').Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hct : c * t' * c⁻¹ = t' := by
      apply Subtype.ext
      have := ((hCmem c).1 c.2).2
      change (c : G) * t * (c : G)⁻¹ = t
      rw [this]
      group
    rw [← conj_zpow, hct]
    exact mem_zpowers_iff.2 ⟨k, rfl⟩
  have ht'p : IsPGroup 2 (zpowers t') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk]
    exact IsPGroup.iff_card.1 htp |>.imp fun i hi => by rwa [Nat.card_zpowers] at hi
  have hle := ht'p.le_sylow_of_normal R
  exact hRx t ⟨t', hle (mem_zpowers t'), rfl⟩

end Lemma37

open Lemma37 in
theorem lemma_3_7 (hK : AschbacherKnownGroupFacts) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (t : G),
      aschbacherThm5IsSemisimple A → t ∈ Subgroup.normalizer (A : Set G) → t ^ 2 = 1 →
      (∃ R : Sylow 2 ↥(A ⊓ Subgroup.centralizer ({t} : Set G)),
        IsCyclic (R : Subgroup ↥(A ⊓ Subgroup.centralizer ({t} : Set G))) ∧ Nat.card R = 4) →
      Open.pRank 2 A = 1 := by
  intro G _ _ A t hA htN ht2 hR
  obtain ⟨R, hRcyc, hRcard⟩ := hR
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, x, hxS, hx4, hxt, htNS, hcent, htA⟩ := setup rfl htN ht2 R hRcyc hRcard
  set S := (S₀ : Subgroup A).map A.subtype with hS
  have hSp : IsPGroup 2 S := S₀.isPGroup'.map _
  have hSA : S ≤ A := map_subtype_le _
  have hmemS : ∀ h : A, (h : G) ∈ S ↔ h ∈ (S₀ : Subgroup A) := by
    intro h
    constructor
    · rintro ⟨h', hh', hh'h⟩
      rwa [← Subtype.ext hh'h]
    · intro hh
      exact ⟨h, hh, rfl⟩
  have hcardS₀ : Nat.card (S₀ : Subgroup A) = Nat.card S := by
    rw [hS, Subgroup.card_map_of_injective A.subtype_injective]
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx4] at this
    norm_num at this
  by_cases huniq : ∀ x₁ x₂ : G, x₁ ∈ S → x₂ ∈ S → x₁ ^ 2 = 1 → x₂ ^ 2 = 1 → x₁ ≠ 1 →
      x₂ ≠ 1 → x₁ = x₂
  · exact pRank_eq_one_of_unique hA S₀ huniq
  exfalso
  push Not at huniq
  obtain ⟨x₁, x₂, hx₁, hx₂, ho₁, ho₂, h₁, h₂, hne⟩ := huniq
  have hSx : ¬ S ≤ zpowers x := fun hle =>
    hne (TwoGroup.involution_unique_of_isCyclic inferInstance (hle hx₁) (hle hx₂) ho₁ h₁ ho₂ h₂)
  have htS : t ∉ S := by
    intro htS'
    have htx : t ∈ zpowers x := hcent t htS' rfl
    apply hSx
    have heq := eq_of_normalizer_le hSp (zpowers_le.2 hxS) fun g hgS hgN => by
      have hgx : g * x * g⁻¹ ∈ zpowers x := (mem_normalizer_iff.1 hgN x).1 (mem_zpowers x)
      have hgx2 : (g * x * g⁻¹) ^ 2 ≠ 1 := by
        rw [conj_pow]
        intro h
        apply hx2
        calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      have hgr : g * x ^ 2 * g⁻¹ = x ^ 2 := by
        rw [← conj_pow]
        rcases mem_zpowers_sq_ne_one hx4 hgx hgx2 with h | h
        · rw [h]
        · rw [h, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
          exact hx4'
      have hgt : g * t = t * g := by
        rcases mem_zpowers_sq_eq_one hx4 htx ht2 with h | h
        · rw [h, mul_one, one_mul]
        · rw [h]
          calc g * x ^ 2 = (g * x ^ 2 * g⁻¹) * g := by group
            _ = x ^ 2 * g := by rw [hgr]
      exact hcent g hgS hgt
    rw [heq]
  have htA' : t ∉ A := fun h => htS (zpowers_le.2 hxS (htA h))
  set T : Set G := {v | ∃ a ∈ A, v = a * t * a⁻¹} with hT
  set P := S ⊔ zpowers t with hP
  have htp : IsPGroup 2 (zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact ht2) : orderOf t ∣ 2 ^ 1)
    exact ⟨i, hi⟩
  have hc : Ctx P S t x T := by
    refine
      { pgroup := hSp.to_sup_of_normal_left' htp (zpowers_le.2 htNS)
        le := le_sup_left
        sup_eq := rfl
        t_normalizer := htNS
        t_sq := ht2
        t_not_mem := htS
        x_mem := hxS
        x_order := hx4
        x_comm := hxt
        cent := hcent
        T_t := ⟨1, one_mem A, by group⟩
        T_conj := ?_
        T_sq := ?_
        T_not_mem := ?_
        T_unique := ?_ }
    · rintro p hp _ ⟨a, haA, rfl⟩
      rcases (mem_sup_zpowers_iff htNS (by rw [ht2]; exact one_mem S)).1 hp with h | h
      · exact ⟨p * a, A.mul_mem (hSA h) haA, by group⟩
      · set c := t⁻¹ * p * a with hcdef
        have hcA : c ∈ A := A.mul_mem (hSA h) haA
        have htcA : t * c * t⁻¹ ∈ A := (mem_normalizer_iff.1 htN c).1 hcA
        refine ⟨t * c * t⁻¹, htcA, ?_⟩
        rw [hcdef]
        group
    · rintro _ ⟨a, -, rfl⟩
      rw [conj_pow, ht2]
      group
    · rintro _ ⟨a, haA, rfl⟩ hv
      apply htA'
      have := A.mul_mem (A.mul_mem (A.inv_mem haA) (hSA hv)) haA
      simpa [mul_assoc] using this
    · rintro _ ⟨a, haA, rfl⟩ w₁ hw₁ w₂ hw₂ hw₁2 hw₂2 hw₁1 hw₂1 hw12 hv₁ hv₂
      have hmemC : ∀ w ∈ S, a * t * a⁻¹ * w = w * (a * t * a⁻¹) →
          a⁻¹ * w * a ∈ A ⊓ centralizer ({t} : Set G) := by
        intro w hw hvw
        refine mem_inf.2 ⟨A.mul_mem (A.mul_mem (A.inv_mem haA) (hSA hw)) haA, ?_⟩
        rw [mem_centralizer_singleton_iff]
        calc a⁻¹ * w * a * t = a⁻¹ * (w * (a * t * a⁻¹)) * a := by group
          _ = a⁻¹ * (a * t * a⁻¹ * w) * a := by rw [hvw]
          _ = t * (a⁻¹ * w * a) := by group
      set e₁ : ↥(A ⊓ centralizer ({t} : Set G)) := ⟨a⁻¹ * w₁ * a, hmemC w₁ hw₁ hv₁⟩ with he₁
      set e₂ : ↥(A ⊓ centralizer ({t} : Set G)) := ⟨a⁻¹ * w₂ * a, hmemC w₂ hw₂ hv₂⟩ with he₂
      have hsq : ∀ w : G, w ^ 2 = 1 → (a⁻¹ * w * a) ^ 2 = 1 := by
        intro w hw
        rw [pow_two]
        calc a⁻¹ * w * a * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a := by group
          _ = 1 := by rw [← pow_two, hw]; group
      have he₁2 : e₁ ^ 2 = 1 := Subtype.ext (by simpa [he₁] using hsq w₁ hw₁2)
      have he₂2 : e₂ ^ 2 = 1 := Subtype.ext (by simpa [he₂] using hsq w₂ hw₂2)
      have he₁1 : e₁ ≠ 1 := fun h => hw₁1 (by
        have := congrArg Subtype.val h
        simp only [he₁, OneMemClass.coe_one] at this
        calc w₁ = a * (a⁻¹ * w₁ * a) * a⁻¹ := by group
          _ = 1 := by rw [this]; group)
      have he₂1 : e₂ ≠ 1 := fun h => hw₂1 (by
        have := congrArg Subtype.val h
        simp only [he₂, OneMemClass.coe_one] at this
        calc w₂ = a * (a⁻¹ * w₂ * a) * a⁻¹ := by group
          _ = 1 := by rw [this]; group)
      have he12 : e₁ * e₂ = e₂ * e₁ := by
        apply Subtype.ext
        simp only [he₁, he₂, Subgroup.coe_mul]
        calc a⁻¹ * w₁ * a * (a⁻¹ * w₂ * a) = a⁻¹ * (w₁ * w₂) * a := by group
          _ = a⁻¹ * (w₂ * w₁) * a := by rw [hw12]
          _ = a⁻¹ * w₂ * a * (a⁻¹ * w₁ * a) := by group
      have hE : IsPGroup 2
          (zpowers e₁ ⊔ zpowers e₂ : Subgroup ↥(A ⊓ centralizer ({t} : Set G))) := by
        have hp₁ : IsPGroup 2 (zpowers e₁) := by
          rw [IsPGroup.iff_card, Nat.card_zpowers, orderOf_eq_prime he₁2 he₁1]
          exact ⟨1, by norm_num⟩
        have hp₂ : IsPGroup 2 (zpowers e₂) := by
          rw [IsPGroup.iff_card, Nat.card_zpowers, orderOf_eq_prime he₂2 he₂1]
          exact ⟨1, by norm_num⟩
        refine hp₁.to_sup_of_normal_left' hp₂ (zpowers_le.2 ?_)
        refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => ?_)
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
        exact (Commute.zpow_left he12 k).eq
      obtain ⟨R', hR'⟩ := hE.exists_le_sylow
      have hR'cyc : IsCyclic (R' : Subgroup ↥(A ⊓ centralizer ({t} : Set G))) :=
        (Sylow.equiv R R').isCyclic.1 hRcyc
      have h12 := TwoGroup.involution_unique_of_isCyclic hR'cyc
        (hR' (mem_sup_left (mem_zpowers e₁))) (hR' (mem_sup_right (mem_zpowers e₂)))
        he₁2 he₁1 he₂2 he₂1
      have := congrArg Subtype.val h12
      simp only [he₁, he₂] at this
      calc w₁ = a * (a⁻¹ * w₁ * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * w₂ * a) * a⁻¹ := by rw [this]
        _ = w₂ := by group
  have hAperf : Group.IsPerfect A := AschbacherTheorem5.semisimple_perfect A hA
  by_cases hgap : ∃ y ∈ S, y ^ 2 = x ^ 2 ∧ t * y * t⁻¹ = y⁻¹ ∧ y * x * y⁻¹ = x⁻¹
  ·
    obtain ⟨y, hyS, hy2, hyt, hxy⟩ := hgap
    have hSP : S ≤ P := le_sup_left
    set S' : Subgroup P := S.subgroupOf P with hS'
    have hS'n : S'.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      exact hc.conj_mem_S g.2 hn
    have hcyc : ∀ B : Subgroup P, B ≤ S' → B.Normal → IsMulCommutative B → IsCyclic B :=
      fun B hBS hBn hBab =>
        gap_abelian_normal_cyclic hc.pgroup hc.t_mem ht2 hcent hx4 hyS hy2 hyt hxy B hBS hBn hBab
    obtain ⟨hshape, -, hcmp⟩ :=
      TwoGroup.dihedral_or_semidihedral_rel hc.pgroup S' hcyc (x₁ := ⟨x₁, hSP hx₁⟩)
        (x₂ := ⟨x₂, hSP hx₂⟩) hx₁ hx₂ (Subtype.ext (by simpa using ho₁))
        (Subtype.ext (by simpa using ho₂)) (fun h => h₁ (congrArg Subtype.val h))
        (fun h => h₂ (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
    have hcmpG : ∀ Y₁ Y₂ : Subgroup G, Y₁ ≤ S → Y₂ ≤ S → ¬ IsCyclic Y₁ → ¬ IsCyclic Y₂ →
        (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, y₁ * y₂ = y₂ * y₁) → Y₂ ≤ Y₁ := by
      intro Y₁ Y₂ h1 h2 hc1 hc2 hcomm
      have hY₁P : Y₁ ≤ P := h1.trans hSP
      have hY₂P : Y₂ ≤ P := h2.trans hSP
      have key := hcmp (Y₁.subgroupOf P) (Y₂.subgroupOf P) (fun x hx => h1 hx)
        (fun x hx => h2 hx)
        (fun hc => hc1 ((Subgroup.subgroupOfEquivOfLe hY₁P).isCyclic.1 hc))
        (fun hc => hc2 ((Subgroup.subgroupOfEquivOfLe hY₂P).isCyclic.1 hc))
        (fun y₁ hy₁ y₂ hy₂ => Subtype.ext (hcomm y₁ hy₁ y₂ hy₂))
      intro y hy
      exact key (show (⟨y, hY₂P hy⟩ : P) ∈ Y₂.subgroupOf P from hy)
    have hAq : Open.IsQuasisimple A := Lemma38.quasisimple_of_comparable hA S₀ hcmpG
    have hiso : (S₀ : Subgroup A) ≃* (S' : Subgroup P) :=
      ((S₀ : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective).trans
        (Subgroup.subgroupOfEquivOfLe hSP).symm
    have hDS : HasDihedralSylowTwo A ∨ HasSemidihedralSylowTwo A := by
      rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · exact Or.inl ⟨S₀, n, hn, ⟨hiso.trans e⟩⟩
      · exact Or.inr ⟨S₀, n, hn, ⟨hiso.trans e⟩⟩
    exact hK.semidihedral_dihedral_no_cyclic_four G A t hAq hDS htN ht2 R ⟨hRcyc, hRcard⟩
  ·
    obtain ⟨ρ, m, hg, hcard⟩ := printed_branch hc hgap
    have hm := hg.1
    rcases (by omega : m = 2 ∨ 3 ≤ m) with hm2 | hm3
    ·
      subst hm2
      have hcx : Nat.card (zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
      rcases hcard with h4 | h8
      · apply hSx
        have heq : zpowers x = S :=
          Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxS) (by rw [h4, hcx]; norm_num)
        rw [heq]
      ·
        obtain ⟨s, hsS, hs2, hsx⟩ : ∃ s ∈ S, s ^ 2 = 1 ∧ s ∉ zpowers x := by
          by_cases hx₁x : x₁ ∈ zpowers x
          · refine ⟨x₂, hx₂, ho₂, fun hx₂x => hne ?_⟩
            exact TwoGroup.involution_unique_of_isCyclic inferInstance hx₁x hx₂x ho₁ h₁ ho₂ h₂
          · exact ⟨x₁, hx₁, ho₁, hx₁x⟩
        have hind : ((zpowers x).subgroupOf S).index = 2 := by
          have h1 := Subgroup.card_mul_index ((zpowers x).subgroupOf S)
          rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hxS)).toEquiv, hcx, h8] at h1
          omega
        have hn := Subgroup.normal_of_index_eq_two hind
        have hsxs : s * x * s⁻¹ ∈ zpowers x := by
          have := hn.conj_mem ⟨x, hxS⟩ (mem_zpowers _ : (⟨x, hxS⟩ : S) ∈ (zpowers x).subgroupOf S)
            ⟨s, hsS⟩
          exact this
        have hsxs2 : (s * x * s⁻¹) ^ 2 ≠ 1 := by
          rw [conj_pow]
          intro h
          apply hx2
          calc x ^ 2 = s⁻¹ * (s * x ^ 2 * s⁻¹) * s := by group
            _ = 1 := by rw [h]; group
        rcases mem_zpowers_sq_ne_one hx4 hsxs hsxs2 with h | h
        ·
          have hxs : x * s = s * x := by
            calc x * s = s * (s⁻¹ * x * s) := by group
              _ = s * x := by
                  congr 1
                  calc s⁻¹ * x * s = s⁻¹ * (s * x * s⁻¹) * s := by rw [h]
                    _ = x := by group
          exact not_abelian_sylow_cyclic_times_two S₀ le_rfl hxS hsS hx4 hs2 hsx hxs h8
        ·
          obtain ⟨hAq, hD⟩ := dihedral_eight hA S₀ hxS hsS hx4 hs2 h hsx h8
          exact hK.semidihedral_dihedral_no_cyclic_four G A t hAq (Or.inl hD) htN ht2 R
            ⟨hRcyc, hRcard⟩
    ·
      set e := ρ ^ 2 ^ (m - 3) * x with he
      have hρS := hg.2.1
      have heS : e ∈ S := S.mul_mem (pow_mem hρS _) hxS
      have he2 : e ^ 2 = 1 := hg.e_sq hc hm3
      have hea : e ∉ zpowers ρ := hg.e_not_mem hc
      have hρe : ρ * e = e * ρ := hg.e_comm
      have hρo : orderOf ρ = 2 ^ (m - 1) := hg.2.2.2.2.1
      rcases hcard with hSm | hSm1
      ·
        refine not_abelian_sylow_cyclic_times_two S₀ (n := m - 1) (by omega) hρS heS hρo he2
          hea hρe ?_
        rw [hSm]
        congr 1
        omega
      ·
        set M := zpowers ρ ⊔ zpowers x with hMdef
        have hMS : M ≤ S := hg.M_le hc
        have hidx : M.relIndex S ≤ 2 := by
          have h1 := Subgroup.relIndex_mul_card (H := M) (K := S)
          rw [inf_of_le_left hMS, hg.card_M hc, hSm1, pow_succ] at h1
          have h2 : 0 < 2 ^ m := by positivity
          rw [mul_comm (2 ^ m) 2] at h1
          have := Nat.eq_of_mul_eq_mul_right h2 h1
          omega
        have hAq : Open.IsQuasisimple A :=
          quasisimple_of_abelian_index_two hA S₀ (M := M) (fun a ha b hb => hg.M_comm ha hb) hidx
            (fun F hFM hF => hg.elem_le_four hc hm3 F hFM hF)
        exact ShapeExclusion.no_quasisimple_shape hAq S₀ (k := m - 1) (by omega) htN ht2 htNS hxS
          hx4 hxt hcent hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1
          (by rw [show m - 1 - 1 = m - 2 by omega]; exact hg.2.2.2.2.2)
          (by rw [← hS, hSm1, show m - 1 + 2 = m + 1 by omega])

end CFSG.ComponentClassification.AschbacherKnownGroup
