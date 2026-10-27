module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdAux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinL2p
import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Components

variable {G : Type} [Group G]

theorem isComponentIn_self {A : Subgroup G} (hA : CFSG.IsQuasisimple ↥A) : IsComponentIn A A := by
  refine ⟨le_rfl, ?_⟩
  have : A.subgroupOf A = ⊤ := Subgroup.subgroupOf_self A
  rw [this]
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hA,
    Subgroup.IsSubnormal.top⟩

theorem commutator_dichotomy {J : Subgroup G} (hJ : CFSG.IsQuasisimple ↥J) {v : G}
    (hv : v ∈ Subgroup.normalizer (J : Set G)) :
    ⁅J, Subgroup.zpowers v⁆ = J ∨ J ≤ Subgroup.centralizer ({v} : Set G) := by
  have hW : ⁅J, Subgroup.zpowers v⁆ ≤ J :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hv)
  have hWn : (⁅J, Subgroup.zpowers v⁆.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).mpr
      (Subgroup.normalizer_commutator_ge_left _ _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ hWn with h1 | h1
  · exact Or.inl (le_antisymm hW (Subgroup.subgroupOf_eq_top.mp h1))
  · right
    have hcen : ⁅⁅J, Subgroup.zpowers v⁆, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      have hxJ : x ∈ J := hW hx
      have hxc := Subgroup.mem_center_iff.mp (h1 (show (⟨x, hxJ⟩ : ↥J) ∈
        ⁅J, Subgroup.zpowers v⁆.subgroupOf J from hx))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hy⟩)
    have hbot : ⁅J, Subgroup.zpowers v⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hJ.1 hcen
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    refine this.trans (Subgroup.centralizer_le ?_)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subgroup.mem_zpowers v

theorem isComponentIn_conjugate_of_mem_normalizer {A P : Subgroup G} (hA : IsComponentIn A P)
    {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    IsComponentIn (CFSG.conjugate A g) P := by
  have h := BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) hA
  have hP : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg
  rw [hP] at h
  exact h

theorem center_eq_bot_of_simple_nonabelian {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases (Subgroup.center Q).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : b ∈ Subgroup.center Q := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp this a)

end Components

section ComponentsFin

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isComponentIn_of_isQuasisimple {K A : Subgroup G} (hK : IsComponentIn K A)
    (hA : CFSG.IsQuasisimple ↥A) : K = A := by
  rcases BenderBranch.eq_or_commute_of_isComponentIn hK (isComponentIn_self hA) with h | h
  · exact h
  · exfalso
    have hqK : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hqK.1
    have hKbot : K = ⊥ := by
      rw [← hperf]
      exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hK.1)
    exact (Subgroup.nontrivial_iff_ne_bot K).mp (CFSG.LocalCores.isQuasisimple_nontrivial hqK) hKbot

theorem pCore_eq_center_of_simple_quotient {J : Subgroup G} (hJ : CFSG.IsQuasisimple ↥J)
    (hs : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J))
    (hnc : ∃ a b : ↥J ⧸ CFSG.pCore 2 ↥J, a * b ≠ b * a) :
    CFSG.pCore 2 ↥J = Subgroup.center ↥J := by
  refine le_antisymm (pCore_le_center_of_isQuasisimple hJ) fun z hz => ?_
  have hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥ :=
    center_eq_bot_of_simple_nonabelian hs hnc
  have hmem : (z : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem false_of_isList_of_hasE9 (hTR : TabThreeRank) {J : Subgroup G}
    (hJ : CFSG.IsQuasisimple ↥J) (hE9 : HasElemAb 3 9 (↥J ⧸ Subgroup.center ↥J))
    (hlist : Is121List (↥J ⧸ CFSG.pCore 2 ↥J)) : False := by
  have hpc := pCore_eq_center_of_simple_quotient hJ hlist.1 hlist.2.1
  obtain ⟨A, hA, hc⟩ := HasElemAb.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpc.symm) hE9
  have := hTR.list _ hlist A hA
  omega

end ComponentsFin

section Conj

variable {G : Type} [Group G]

theorem conjugate_sup (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem conjugate_commutator (A B : Subgroup G) (g : G) :
    ⁅CFSG.conjugate A g, CFSG.conjugate B g⁆ = CFSG.conjugate ⁅A, B⁆ g := by
  unfold CFSG.conjugate
  exact (Subgroup.map_commutator _ _ _).symm

theorem conj_involution_mem {A B : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hB : B = CFSG.conjugate A t) {x : G} (hx : x ∈ A) : t * x * t ∈ B := by
  rw [hB, BenderBranch.mem_conjugate_iff]
  have : t * (t * x * t) * t⁻¹ = x := by
    calc t * (t * x * t) * t⁻¹ = (t * t) * x * (t * t⁻¹) := by group
      _ = x := by rw [ht2]; group
  rw [this]
  exact hx

theorem conj_involution_mem' {A B : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hB : B = CFSG.conjugate A t) {y : G} (hy : y ∈ B) : t * y * t ∈ A := by
  rw [hB, BenderBranch.mem_conjugate_iff] at hy
  have h1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [h1] at hy
  exact hy

theorem diag_mem_centralizer {A B : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hB : B = CFSG.conjugate A t) (hc : ⁅A, B⁆ = ⊥) {x : G} (hx : x ∈ A) :
    x * (t * x * t) ∈ Subgroup.centralizer ({t} : Set G) := by
  have hcomm : x * (t * x * t) = (t * x * t) * x :=
    BenderBranch.commute_of_commutator_eq_bot hc hx (conj_involution_mem ht2 hB hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : x * (t * x * t) * t = x * t * x := by
    calc x * (t * x * t) * t = x * (t * x) * (t * t) := by group
      _ = x * t * x := by rw [ht2]; group
  have e2 : t * (x * (t * x * t)) = x * t * x := by
    calc t * (x * (t * x * t)) = t * ((t * x * t) * x) := by rw [hcomm]
      _ = (t * t) * x * t * x := by group
      _ = x * t * x := by rw [ht2]; group
  rw [e1, e2]

theorem exists_diag {A B : Subgroup G} {t : G} (ht2 : t * t = 1) (hB : B = CFSG.conjugate A t)
    (hAB : A ⊓ B = ⊥) (hc : ⁅A, B⁆ = ⊥) {z : G} (hz : z ∈ A ⊔ B)
    (hzt : z ∈ Subgroup.centralizer ({t} : Set G)) : ∃ x ∈ A, z = x * (t * x * t) := by
  have hc' : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot hc ha hb
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc').mp hz
  have hzt' : a * b * t = t * (a * b) := Subgroup.mem_centralizer_singleton_iff.mp hzt
  have h1 : (t * b * t) * (t * a * t) = a * b := by
    calc (t * b * t) * (t * a * t) = t * (b * a) * t := by
          calc (t * b * t) * (t * a * t) = t * b * (t * t) * a * t := by group
            _ = t * (b * a) * t := by rw [ht2]; group
      _ = t * (a * b) * t := by rw [hc' a ha b hb]
      _ = a * b := by
          calc t * (a * b) * t = t * (a * b * t) := by group
            _ = t * (t * (a * b)) := by rw [hzt']
            _ = (t * t) * (a * b) := by group
            _ = a * b := by rw [ht2, one_mul]
  have h2 := eq_and_eq_of_mul_eq_mul hAB (conj_involution_mem' ht2 hB hb) ha
    (conj_involution_mem ht2 hB ha) hb h1
  exact ⟨a, ha, by rw [h2.2]⟩

variable [Finite G]

theorem card_diag_le {A B : Subgroup G} {t : G} (ht2 : t * t = 1) (hB : B = CFSG.conjugate A t)
    (hAB : A ⊓ B = ⊥) (hc : ⁅A, B⁆ = ⊥) :
    Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card ↥A := by
  classical
  let f : ↥((A ⊔ B) ⊓ Subgroup.centralizer ({t} : Set G)) → ↥A := fun z =>
    ⟨Classical.choose (exists_diag ht2 hB hAB hc z.2.1 z.2.2),
      (Classical.choose_spec (exists_diag ht2 hB hAB hc z.2.1 z.2.2)).1⟩
  have hinj : Function.Injective f := by
    intro z z' h
    apply Subtype.ext
    have e1 := (Classical.choose_spec (exists_diag ht2 hB hAB hc z.2.1 z.2.2)).2
    have e2 := (Classical.choose_spec (exists_diag ht2 hB hAB hc z'.2.1 z'.2.2)).2
    have hx : Classical.choose (exists_diag ht2 hB hAB hc z.2.1 z.2.2) =
        Classical.choose (exists_diag ht2 hB hAB hc z'.2.1 z'.2.2) := congrArg Subtype.val h
    rw [e1, e2, hx]
  exact Nat.card_le_card_of_injective f hinj

theorem eq_diag_of_le_of_card_ge {A B K : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hB : B = CFSG.conjugate A t) (hAB : A ⊓ B = ⊥) (hc : ⁅A, B⁆ = ⊥)
    (hK : K ≤ (A ⊔ B) ⊓ Subgroup.centralizer ({t} : Set G)) (hcard : Nat.card ↥A ≤ Nat.card ↥K) :
    K = (A ⊔ B) ⊓ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.eq_of_le_of_card_ge hK ((card_diag_le ht2 hB hAB hc).trans hcard)

theorem conj_eq_or_conj_eq {A : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hA : IsComponentIn A (A ⊔ CFSG.conjugate A t)) {r : G}
    (hr : r ∈ Subgroup.normalizer ((A ⊔ CFSG.conjugate A t : Subgroup G) : Set G)) :
    CFSG.conjugate A r = A ∨ CFSG.conjugate A r = CFSG.conjugate A t := by
  set P : Subgroup G := A ⊔ CFSG.conjugate A t with hP
  have htP : t ∈ Subgroup.normalizer (P : Set G) := by
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, hP, conjugate_sup,
      BenderBranch.conjugate_conjugate, ht2, BenderBranch.conjugate_one, sup_comm]
  have hAt : IsComponentIn (CFSG.conjugate A t) P :=
    isComponentIn_conjugate_of_mem_normalizer hA htP
  have hAr : IsComponentIn (CFSG.conjugate A r) P :=
    isComponentIn_conjugate_of_mem_normalizer hA hr
  by_cases h1 : CFSG.conjugate A r = A
  · exact Or.inl h1
  by_cases h2 : CFSG.conjugate A r = CFSG.conjugate A t
  · exact Or.inr h2
  exfalso
  have hc1 : ⁅CFSG.conjugate A r, A⁆ = ⊥ := (BenderBranch.eq_or_commute_of_isComponentIn hAr hA).resolve_left h1
  have hc2 : ⁅CFSG.conjugate A r, CFSG.conjugate A t⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hAr hAt).resolve_left h2
  have hqr : CFSG.IsQuasisimple ↥(CFSG.conjugate A r) := BenderBranch.isQuasisimple_of_isComponentIn hAr
  have hperf : ⁅CFSG.conjugate A r, CFSG.conjugate A r⁆ = CFSG.conjugate A r :=
    Subgroup.isPerfect_iff.mp hqr.1
  have hc1' : ⁅A, CFSG.conjugate A r⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc1
  have hc2' : ⁅CFSG.conjugate A t, CFSG.conjugate A r⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hc2
  have hcP : CFSG.conjugate A r ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : P ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact BenderBranch.commute_of_commutator_eq_bot hc1' ha hx
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact BenderBranch.commute_of_commutator_eq_bot hc2' ha hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hy)
  have hbot : ⁅CFSG.conjugate A r, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcP
  have : CFSG.conjugate A r = ⊥ := by
    rw [← hperf]
    exact le_bot_iff.mp (hbot ▸ Subgroup.commutator_mono le_rfl hAr.1)
  exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hqr) this

omit [Finite G] in
theorem sup_eq_of_mem_pair {x₁ x₂ a b c d : Subgroup G}
    (ha : a = x₁ ∨ a = x₂) (hb : b = x₁ ∨ b = x₂) (hc : c = x₁ ∨ c = x₂) (hd : d = x₁ ∨ d = x₂)
    (hab : a ≠ b) (hcd : c ≠ d) : c ⊔ d = a ⊔ b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;>
    first | exact absurd rfl hab | exact absurd rfl hcd | rfl | exact sup_comm _ _

omit [Finite G] in
theorem normalizes_sup_of_two_orbit {H A : Subgroup G}
    (hcard : Nat.card {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate A h} = 2) {t : G}
    (ht : t ∈ H) (hne : CFSG.conjugate A t ≠ A) :
    H ≤ Subgroup.normalizer ((A ⊔ CFSG.conjugate A t : Subgroup G) : Set G) := by
  intro y hy
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, conjugate_sup,
    BenderBranch.conjugate_conjugate]
  obtain ⟨x₁, x₂, hx12, hx⟩ := Nat.card_eq_two_iff.mp hcard
  have hall : ∀ L' : Subgroup G, (∃ h ∈ H, L' = CFSG.conjugate A h) → L' = x₁.1 ∨ L' = x₂.1 := by
    intro L' hL'
    have : (⟨L', hL'⟩ : {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate A h}) ∈ ({x₁, x₂} : Set _) := by
      rw [hx]; trivial
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hA : ∃ h ∈ H, A = CFSG.conjugate A h := ⟨1, H.one_mem, (BenderBranch.conjugate_one A).symm⟩
  have hAt : ∃ h ∈ H, CFSG.conjugate A t = CFSG.conjugate A h := ⟨t, ht, rfl⟩
  have hAy : ∃ h ∈ H, CFSG.conjugate A y = CFSG.conjugate A h := ⟨y, hy, rfl⟩
  have hAty : ∃ h ∈ H, CFSG.conjugate A (t * y) = CFSG.conjugate A h := ⟨t * y, H.mul_mem ht hy, rfl⟩
  have hne2 : CFSG.conjugate A y ≠ CFSG.conjugate A (t * y) := by
    intro h
    rw [← BenderBranch.conjugate_conjugate] at h
    exact hne (BenderBranch.conjugate_inj.mp h.symm)
  exact sup_eq_of_mem_pair (hall _ hA) (hall _ hAt) (hall _ hAy) (hall _ hAty) hne.symm hne2

end Conj

section Nine3

variable {G : Type} [Group G] [Finite G]

theorem exists_E9_of_commute {x y : G} (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxy : x * y = y * x) (hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    ∃ A : Subgroup G, A = Subgroup.zpowers x ⊔ Subgroup.zpowers y ∧ IsElemAbelian 3 A ∧
      Nat.card A = 9 := by
  have hxyC : Commute x y := hxy
  have hc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hxyC.zpow_zpow m n).eq
  have hex : ∀ a ∈ Subgroup.zpowers x, a ^ 3 = 1 := fun a ha => by
    have := pow_card_eq_one' (G := ↥(Subgroup.zpowers x)) (x := ⟨a, ha⟩)
    rw [Nat.card_zpowers, hx] at this
    exact congrArg Subtype.val this
  have hey : ∀ a ∈ Subgroup.zpowers y, a ^ 3 = 1 := fun a ha => by
    have := pow_card_eq_one' (G := ↥(Subgroup.zpowers y)) (x := ⟨a, ha⟩)
    rw [Nat.card_zpowers, hy] at this
    exact congrArg Subtype.val this
  have hform : ∀ a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, ∃ m n : ℤ, a = x ^ m * y ^ n := by
    intro a ha
    obtain ⟨h, hh, k, hk, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨m, n, rfl⟩
  have hxx : ∀ m m' : ℤ, Commute (x ^ m) (x ^ m') := fun m m' => (Commute.refl x).zpow_zpow m m'
  have hyy : ∀ n n' : ℤ, Commute (y ^ n) (y ^ n') := fun n n' => (Commute.refl y).zpow_zpow n n'
  have hxy' : ∀ m n : ℤ, Commute (x ^ m) (y ^ n) := fun m n => hxyC.zpow_zpow m n
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers y, rfl, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨m, n, ha⟩ := hform a a.2
    obtain ⟨m', n', hb⟩ := hform b b.2
    show (a : G) * b = b * a
    rw [ha, hb]
    exact (Commute.mul_left (Commute.mul_right (hxx m m') (hxy' m n'))
      (Commute.mul_right (hxy' m' n).symm (hyy n n'))).eq
  · obtain ⟨m, n, rfl⟩ := hform a ha
    rw [(hxy' m n).mul_pow, hex _ (Subgroup.zpow_mem_zpowers x m), hey _ (Subgroup.zpow_mem_zpowers y n),
      one_mul]
  · rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot hc hinf, Nat.card_zpowers, Nat.card_zpowers,
      hx, hy]

end Nine3

section Misc

variable {G : Type} [Group G]

omit [Group G] in
theorem isFermatOrMersenne_seven : IsFermatOrMersenne 7 :=
  ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩

theorem psl2_seven_of_psl3_two {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 2 1) :
    StatedClassicalModel X .PSL 2 7 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two h

theorem IsL2pType.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsL2pType Y) :
    IsL2pType X := by
  rcases h with ⟨p, hp, h7, hm⟩ | hm
  · exact Or.inl ⟨p, hp, h7, Unc25Small.statedClassicalModel_psl_of_mulEquiv e hm⟩
  · exact Or.inr (Unc25Small.statedClassicalModel_psl_of_mulEquiv e hm)

theorem exists_order_three_of_isL2pType {X : Type} [Group X] (h : IsL2pType X) :
    ∃ a : X, orderOf a = 3 := by
  obtain ⟨F, _, _, p, hp, hp7, hF, -, ⟨e⟩⟩ := Out21.model_of_isL2pType h
  have hpodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have h3p : ¬ 3 ∣ p := by
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h3
    omega
  obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := by
    obtain ⟨k, hk⟩ := hpodd
    exact ⟨k + 1, by omega⟩
  have hcard : Nat.card X = p * (m * (p - 1)) := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F (Out21.hodd_of hp7 hF), hF]
    have hsq : p ^ 2 - 1 = 2 * (m * (p - 1)) := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have h1 : (q + 1) ^ 2 - 1 = q * (q + 2) := by
        have : (q + 1) ^ 2 = q * (q + 2) + 1 := by ring
        omega
      have hq2 : q + 2 = 2 * m := by omega
      rw [h1, hq2]
      simp only [Nat.add_sub_cancel]
      ring
    rw [hsq, show p * (2 * (m * (p - 1))) = 2 * (p * (m * (p - 1))) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hne : Nat.card X ≠ 0 := by
    rw [hcard]
    have : 0 < p := by omega
    have : 0 < m := by omega
    have : 0 < p - 1 := by omega
    positivity
  have : Finite X := Nat.finite_of_card_ne_zero hne
  have h3 : 3 ∣ Nat.card X := by
    rw [hcard]
    have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hp3 with h1 | h1
    · have h3' : 3 ∣ p - 1 := by omega
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h3' m) p
    · have h3' : 3 ∣ p + 1 := by omega
      have h3m : 3 ∣ m := by omega
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3m (p - 1)) p
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 h3

theorem relIndex_le_two_of_forall {Y Y₀ : Subgroup G}
    (h : ∀ a ∈ Y, a ∉ Y₀ → ∀ b ∈ Y, Xor (b * a ∈ Y₀) (b ∈ Y₀)) : Y₀.relIndex Y ≤ 2 := by
  by_cases hY : Y ≤ Y₀
  · rw [Subgroup.relIndex_eq_one.mpr hY]; norm_num
  · obtain ⟨a, haY, haY₀⟩ := Set.not_subset.mp hY
    rw [Subgroup.relIndex_eq_two_iff.mpr ⟨a, haY, h a haY haY₀⟩]

theorem mem_normalizer_inf {A B : Subgroup G} {c : G} (hA : c ∈ Subgroup.normalizer (A : Set G))
    (hB : c ∈ Subgroup.normalizer (B : Set G)) : c ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, BenderBranch.conjugate_inf,
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hA,
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hB]

theorem mem_normalizer_centralizer {A : Subgroup G} {c : G}
    (hA : c ∈ Subgroup.normalizer (A : Set G)) :
    c ∈ Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, BenderBranch.conjugate_centralizer,
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hA]

theorem perfectResidualOf_of_perfect {D : Subgroup G} (hD : ⁅D, D⁆ = D) :
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf D = D := by
  have hP : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hD
  unfold CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
  have : (⨅ n, derivedSeries ↥D n) = ⊤ := by
    simp [Group.IsPerfect.derivedSeries_eq_top]
  rw [this, Subgroup.map_top, Subgroup.range_subtype]

end Misc

section Types

variable {G : Type} [Group G]

theorem nonempty_conjugateEquiv (H : Subgroup G) (g : G) :
    Nonempty (↥H ≃* ↥(CFSG.conjugate H g)) :=
  ⟨Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective⟩

theorem IsKType.of_isL2pType {X : Subgroup G} (h : IsL2pType ↥X) : IsKType X := by
  rcases h with ⟨p, hp, h7, hm⟩ | hm
  · exact Or.inl ⟨p, hp, h7, hm⟩
  · exact Or.inr (Or.inl hm)

theorem isL32_of_isL2pType_of_not_big {X : Subgroup G} (h : IsL2pType ↥X) (hn : ¬ IsL2pBig X) :
    IsL32 X := by
  rcases h with ⟨p, hp, h7, hm⟩ | hm
  · exact absurd ⟨p, hp, h7, hm⟩ hn
  · exact hm

theorem isCaseGroup_of_pat {X K : Subgroup G} {t : G}
    (h : PatA X K t ∨ PatB X K t ∨ PatSp4 X K ∨ PatL5 X K ∨ PatHS X K t ∨ PatA8 X K t) :
    IsCaseGroup X := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h.2.1
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))
  · exact Or.inr (Or.inr (Or.inl h.2.1))
  · obtain ⟨-, φ, -⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ⟩)))

theorem inf_eq_bot_of_center_eq_bot {A B : Subgroup G} (hc : ⁅A, B⁆ = ⊥)
    (hZ : Subgroup.center ↥A = ⊥) : A ⊓ B = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxc : ∀ y ∈ A, y * x = x * y := fun y hy =>
    BenderBranch.commute_of_commutator_eq_bot hc hy hx.2
  have hmem : (⟨x, hx.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Types

section Elementary2

variable {G : Type} [Group G]

theorem commutator_zpowers_eq_bot_of_commute {A : Subgroup G} {t : G}
    (h : ∀ a ∈ A, a * t = t * a) : ⁅A, Subgroup.zpowers t⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
  exact (Commute.zpow_left (show Commute t a from (h a ha).symm) n).eq

theorem eq_one_of_isPGroup_two_of_pow_three {Y : Type} [Group Y] {P : Subgroup Y}
    (hP : IsPGroup 2 P) {x : Y} (hx : x ∈ P) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, hx⟩ : P)).trans hk
  have h3' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hk'] at h3'
  have : (2 ^ k).Coprime 3 := Nat.Coprime.pow_left _ (by norm_num)
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd this h3'
  rw [h1] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem exists_noncomm_of_perfect {Q : Type*} [Group Q] [Nontrivial Q] (h : Group.IsPerfect Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have := h
  exact Group.IsPerfect.not_isSolvable Q inferInstance

end Elementary2

section PerfectResidual

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
open CFSG.RankThreeCoreUniqueness.Helpers in
theorem perfectResidualOf_le (X : Subgroup G) : perfectResidualOf X ≤ X :=
  Subgroup.map_subtype_le _

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem perfectResidualOf_perfect (X : Subgroup G) :
    ⁅perfectResidualOf X, perfectResidualOf X⁆ = perfectResidualOf X :=
  Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect X)

omit [Finite G] in
open CFSG.RankThreeCoreUniqueness.Helpers in
theorem le_perfectResidualOf {P X : Subgroup G} (hP : ⁅P, P⁆ = P) (hPX : P ≤ X) :
    P ≤ perfectResidualOf X := by
  set Q : Subgroup ↥X := P.comap X.subtype with hQ
  have hQmap : Q.map X.subtype = P := by
    rw [hQ, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hPX
  have hQperf : ⁅Q, Q⁆ = Q := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hQmap, hP]
  have hder : ∀ n : ℕ, Q ≤ derivedSeries ↥X n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
        rw [derivedSeries_succ]
        calc Q = ⁅Q, Q⁆ := hQperf.symm
          _ ≤ ⁅derivedSeries ↥X n, derivedSeries ↥X n⁆ := Subgroup.commutator_mono ih ih
  have hle : Q ≤ perfectResidual ↥X := le_iInf hder
  calc P = Q.map X.subtype := hQmap.symm
    _ ≤ (perfectResidual ↥X).map X.subtype := Subgroup.map_mono hle

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem perfectResidualOf_conjugate (X : Subgroup G) (g : G) :
    perfectResidualOf (CFSG.conjugate X g) = CFSG.conjugate (perfectResidualOf X) g := by
  apply le_antisymm
  · have hperf : ⁅CFSG.conjugate (perfectResidualOf (CFSG.conjugate X g)) g⁻¹,
        CFSG.conjugate (perfectResidualOf (CFSG.conjugate X g)) g⁻¹⁆ =
        CFSG.conjugate (perfectResidualOf (CFSG.conjugate X g)) g⁻¹ := by
      rw [conjugate_commutator, perfectResidualOf_perfect]
    have hle : CFSG.conjugate (perfectResidualOf (CFSG.conjugate X g)) g⁻¹ ≤ X := by
      have := BenderBranch.conjugate_mono (perfectResidualOf_le (CFSG.conjugate X g)) g⁻¹
      rwa [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one] at this
    have hQ := le_perfectResidualOf hperf hle
    have := BenderBranch.conjugate_mono hQ g
    rwa [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one] at this
  · refine le_perfectResidualOf ?_ (BenderBranch.conjugate_mono (perfectResidualOf_le X) g)
    rw [conjugate_commutator, perfectResidualOf_perfect]

end PerfectResidual

end CFSG.QuasithinUnique.Id2519
