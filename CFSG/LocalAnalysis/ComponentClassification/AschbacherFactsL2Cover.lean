module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open

@[expose] def FourGroupGenerationCore : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] [IsSimpleGroup Q], HasDihedralSylowTwo Q →
    ∀ α β : MulAut Q, α * β = β * α → α ^ 2 = 1 → β ^ 2 = 1 → α ≠ 1 → β ≠ 1 → α ≠ β →
    ∀ H : Subgroup Q,
      (∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ x ∈ H, γ x ∈ H) →
      (∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ x : Q, γ x = x → Odd (orderOf x) → x ∈ H) →
      (∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ t : Q, t ^ 2 = 1 → t ≠ 1 →
        γ = MulAut.conj t → ∀ y : Q, t ∈ Subgroup.zpowers y → y ∈ H) →
      H = ⊤ ∨ (IsSmallDihedralSimple Q ∧ ∃ a b : Q, α = MulAut.conj a ∧ β = MulAut.conj b)

theorem mulAut_eq_one_of_mod_center {L : Type*} [Group L] (hp : commutator L = ⊤)
    (φ : MulAut L) (hφ : ∀ x, x⁻¹ * φ x ∈ Subgroup.center L) : φ = 1 := by
  let c : L →* Subgroup.center L :=
    { toFun := fun x => ⟨x⁻¹ * φ x, hφ x⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        have hc : ∀ z : L, x⁻¹ * φ x * z = z * (x⁻¹ * φ x) := fun z =>
          (Subgroup.mem_center_iff.mp (hφ x) z).symm
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (φ x * φ y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by group
          _ = x⁻¹ * φ x * y⁻¹ * φ y := by rw [← hc y⁻¹]
          _ = x⁻¹ * φ x * (y⁻¹ * φ y) := by group }
  have hker : commutator L ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hp] at hker
  ext x
  have hx : c x = 1 := hker (Subgroup.mem_top x)
  have h1 : x⁻¹ * φ x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  calc φ x = x * (x⁻¹ * φ x) := by group
    _ = x := by rw [h1, mul_one]

theorem exists_odd_lift {L : Type*} [Group L] [Finite L] (N : Subgroup L) [N.Normal]
    (xb : L ⧸ N) (hxb : Odd (orderOf xb)) :
    ∃ x : L, (x : L ⧸ N) = xb ∧ Odd (orderOf x) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective xb
  set k := orderOf (y : L ⧸ N) with hk
  set a := (orderOf y).factorization 2 with ha
  have hcop : Nat.Coprime (2 ^ a) k := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxb)
  have hk1 : 1 ≤ k := (orderOf_pos _)
  rcases Nat.lt_or_ge 1 k with hk2 | hk2
  · obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk2
    refine ⟨y ^ (2 ^ a * e), ?_, ?_⟩
    · rw [QuotientGroup.mk_pow, ← pow_mod_orderOf, ← hk, he, pow_one]
    · obtain ⟨b, hb, hbodd⟩ : ∃ b, orderOf y = 2 ^ a * b ∧ Odd b := by
        refine ⟨orderOf y / 2 ^ a, (Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)).symm, ?_⟩
        rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
        exact Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos y).ne'
      apply Odd.of_dvd_nat hbodd
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm (2 ^ a * e), ← mul_assoc, mul_comm b, ← hb, pow_mul,
        pow_orderOf_eq_one, one_pow]
  · have hk1' : k = 1 := by omega
    refine ⟨1, ?_, by simp⟩
    rw [QuotientGroup.mk_one]
    exact (orderOf_eq_one_iff.mp hk1').symm

theorem exists_fixed_of_odd_mod_center {L : Type*} [Group L] (β : MulAut L)
    (hβ : ∀ x, β (β x) = x) (x : L) (hx : x⁻¹ * β x ∈ Subgroup.center L)
    (hodd : Odd (orderOf (x⁻¹ * β x))) :
    ∃ z ∈ Subgroup.center L, β (x * z) = x * z := by
  set c := x⁻¹ * β x with hcdef
  have hβx : β x = x * c := by rw [hcdef]; group
  have hβc : β c = c⁻¹ := by
    have h1 : β (β x) = x * c * β c := by rw [hβx, map_mul, hβx]
    rw [hβ] at h1
    have h2 : c * β c = 1 := by
      have := congrArg (fun y => x⁻¹ * y) h1
      simp only [inv_mul_cancel, ← mul_assoc] at this
      rw [this]
      group
    exact eq_inv_of_mul_eq_one_right h2
  obtain ⟨m, hm⟩ := hodd
  refine ⟨c ^ (m + 1), Subgroup.pow_mem _ hx _, ?_⟩
  rw [map_mul, map_pow, hβc, hβx, inv_pow]
  have hc : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
  calc x * c * (c ^ (m + 1))⁻¹ = x * (c * (c ^ (m + 1))⁻¹) := by group
    _ = x * c ^ (m + 1) := by
      congr 1
      have h1 : c ^ (2 * m + 1) = c ^ (m + 1) * c ^ m := by rw [← pow_add]; ring_nf
      rw [hc] at h1
      have h2 : (c ^ (m + 1))⁻¹ = c ^ m := (eq_inv_of_mul_eq_one_right h1.symm).symm
      rw [h2, ← pow_succ']

theorem eq_top_of_sup_center_eq_top {L : Type*} [Group L] (hp : commutator L = ⊤)
    {C : Subgroup L} (h : C ⊔ Subgroup.center L = ⊤) : C = ⊤ := by
  rw [eq_top_iff, ← hp, _root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ C ⊔ Subgroup.center L := h ▸ Subgroup.mem_top x
  have hy : y ∈ C ⊔ Subgroup.center L := h ▸ Subgroup.mem_top y
  obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have h1 : ∀ g : L, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.mp hz₁ g).symm
  have h2 : ∀ g : L, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.mp hz₂ g).symm
  rw [commutatorElement_def]
  have hA : c₁ * z₁ * (c₂ * z₂) = c₁ * c₂ * (z₁ * z₂) :=
    Commute.mul_mul_mul_comm (h1 c₂) c₁ z₂
  have hB : c₂ * z₂ * (c₁ * z₁) = c₂ * c₁ * (z₂ * z₁) :=
    Commute.mul_mul_mul_comm (h2 c₁) c₂ z₁
  have hz : z₁ * z₂ = z₂ * z₁ := h1 z₂
  have : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
    calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
        (c₁ * z₁ * (c₂ * z₂)) * (c₂ * z₂ * (c₁ * z₁))⁻¹ := by group
      _ = (c₁ * c₂ * (z₁ * z₂)) * (c₂ * c₁ * (z₂ * z₁))⁻¹ := by rw [hA, hB]
      _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by rw [hz]; group
  rw [this]
  exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)

theorem exists_fourGroup_generators {G : Type*} [Group G] {U : Subgroup G} (hU : IsFourGroup U) :
    ∃ u₁ u₂ : G, u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧
      ∀ u ∈ U, u = 1 ∨ u = u₁ ∨ u = u₂ ∨ u = u₁ * u₂ := by
  classical
  obtain ⟨⟨hcomm⟩, hsq⟩ := hU.1
  have hcard := hU.2
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let _ : Fintype U := Fintype.ofFinite U
  have hcardF : Fintype.card U = 4 := by rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨a, ha⟩ : ∃ a : U, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card U ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => by rw [h a, h b])
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : U, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset U) ⊆ {1, a} := by
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcardF] at this
    have h2 := Finset.card_le_two (a := (1 : U)) (b := a)
    omega
  have hsq' : ∀ x : U, x ^ 2 = 1 := fun x => Subtype.ext (hsq x x.2)
  have hab : (a : G) * b = b * a := congrArg Subtype.val (hcomm.comm a b)
  refine ⟨a, b, a.2, b.2, fun h => ha (Subtype.ext h), fun h => hb1 (Subtype.ext h),
    fun h => hba (Subtype.ext h).symm, ?_⟩
  intro u hu
  let x : U := ⟨u, hu⟩
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq' a)]
  have habA : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habB : a * b ≠ b := fun h => ha (by simpa using h)
  have e1 : (1 : U) ∉ ({a, b, a * b} : Finset U) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb1, Ne.symm hab1⟩
  have e2 : a ∉ ({b, a * b} : Finset U) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hba, Ne.symm habA⟩
  have hc4 : ({1, a, b, a * b} : Finset U).card = 4 := by
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_pair (Ne.symm habB)]
  have hall : (Finset.univ : Finset U) = {1, a, b, a * b} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, hcardF, hc4])).symm
  have hx : x ∈ (Finset.univ : Finset U) := Finset.mem_univ x
  rw [hall] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

section Induced

variable {G : Type*} [Group G] (L : Subgroup G)

@[expose] def conjAutOf {u : G} (hu : u ∈ Subgroup.normalizer (L : Set G)) : MulAut L :=
  restrictMulAut (MulAut.conj u) L (fun x => by
    rw [MulAut.conj_apply]
    exact Subgroup.mem_normalizer_iff.mp hu x)

theorem conjAutOf_apply {u : G} (hu : u ∈ Subgroup.normalizer (L : Set G)) (x : L) :
    (conjAutOf L hu x : G) = u * x * u⁻¹ := rfl

@[expose] def quotAutOf {u : G} (hu : u ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (L ⧸ Subgroup.center L) :=
  QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) (conjAutOf L hu)
    (Subgroup.map_center_eq _)

theorem quotAutOf_mk {u : G} (hu : u ∈ Subgroup.normalizer (L : Set G)) (x : L) :
    quotAutOf L hu (x : L ⧸ Subgroup.center L) =
      ((conjAutOf L hu x : L) : L ⧸ Subgroup.center L) := rfl

theorem quotAutOf_mul {u v : G} (hu : u ∈ Subgroup.normalizer (L : Set G))
    (hv : v ∈ Subgroup.normalizer (L : Set G)) :
    quotAutOf L (Subgroup.mul_mem _ hu hv) = quotAutOf L hu * quotAutOf L hv := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.mul_apply, quotAutOf_mk, quotAutOf_mk, quotAutOf_mk]
  congr 1
  apply Subtype.ext
  rw [conjAutOf_apply, conjAutOf_apply, conjAutOf_apply]
  group

theorem quotAutOf_one : quotAutOf L (Subgroup.one_mem _) = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [quotAutOf_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [conjAutOf_apply]
  group

theorem conjAutOf_eq_of_quotAutOf (hp : commutator L = ⊤) {u : G}
    (hu : u ∈ Subgroup.normalizer (L : Set G)) (a : L)
    (h : quotAutOf L hu = MulAut.conj (a : L ⧸ Subgroup.center L)) :
    conjAutOf L hu = MulAut.conj a := by
  have h1 := mulAut_eq_one_of_mod_center hp ((MulAut.conj a)⁻¹ * conjAutOf L hu) (by
    intro x
    rw [← QuotientGroup.eq]
    have h2 := DFunLike.congr_fun h (x : L ⧸ Subgroup.center L)
    rw [quotAutOf_mk, MulAut.conj_apply] at h2
    have h3 : ((MulAut.conj a)⁻¹ * conjAutOf L hu) x = a⁻¹ * conjAutOf L hu x * a := by
      rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [h3, QuotientGroup.mk_mul, QuotientGroup.mk_mul, h2, QuotientGroup.mk_inv]
    group)
  calc conjAutOf L hu = MulAut.conj a * ((MulAut.conj a)⁻¹ * conjAutOf L hu) := by group
    _ = MulAut.conj a := by rw [h1, mul_one]

theorem mem_sup_centralizer_of_conjAutOf {u : G} (hu : u ∈ Subgroup.normalizer (L : Set G))
    (a : L) (h : conjAutOf L hu = MulAut.conj a) : u ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hc : u * (a : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    set y : L := a⁻¹ * ⟨x, hx⟩ * a with hydef
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h y)
    rw [conjAutOf_apply, MulAut.conj_apply] at h1
    have hy : (y : G) = (a : G)⁻¹ * x * a := by simp [hydef]
    have hay : ((a * y * a⁻¹ : L) : G) = x := by simp [hydef]; group
    rw [hay, hy] at h1
    calc x * (u * (a : G)⁻¹) = (u * ((a : G)⁻¹ * x * a) * u⁻¹) * (u * (a : G)⁻¹) := by
          rw [h1]
      _ = u * (a : G)⁻¹ * x := by group
  have : u = u * (a : G)⁻¹ * a := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left a.2)

end Induced

theorem mem_centralizerJoin_of {G : Type*} [Group G] {U L : Subgroup G} {u x : G} (hu : u ∈ U)
    (hu1 : u ≠ 1) (hxL : x ∈ L) (hxu : x * u = u * x) : x ∈ centralizerJoin U L :=
  Subgroup.mem_iSup_of_mem u (Subgroup.mem_iSup_of_mem hu (Subgroup.mem_iSup_of_mem hu1
    (Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr hxu⟩)))

theorem conj_mem_centralizerJoin {G : Type*} [Group G] {U L : Subgroup G}
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {w : G} (hw : w ∈ U)
    (hwN : w ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ centralizerJoin U L) :
    w * x * w⁻¹ ∈ centralizerJoin U L := by
  have hle : centralizerJoin U L ≤ (centralizerJoin U L).comap (MulAut.conj w).toMonoidHom := by
    refine (iSup_le fun u => iSup_le fun hu => iSup_le fun hu1 => ?_ : centralizerJoin U L ≤ _)
    intro y hy
    obtain ⟨hyL, hyu⟩ := Subgroup.mem_inf.mp hy
    have hyu' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyu
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    apply mem_centralizerJoin_of hu hu1 ((Subgroup.mem_normalizer_iff.mp hwN y).mp hyL)
    have hwu : w * u = u * w := hUc w hw u hu
    have hwu' : w⁻¹ * u = u * w⁻¹ := by
      calc w⁻¹ * u = w⁻¹ * (u * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * u) * w⁻¹ := by rw [hwu]
        _ = u * w⁻¹ := by group
    calc w * y * w⁻¹ * u = w * y * (w⁻¹ * u) := by group
      _ = w * (y * u) * w⁻¹ := by rw [hwu']; group
      _ = w * (u * y) * w⁻¹ := by rw [hyu']
      _ = (w * u) * y * w⁻¹ := by group
      _ = u * (w * y * w⁻¹) := by rw [hwu]; group
  exact hle hx

theorem dihedral_cover_generation_of_core (hcore : FourGroupGenerationCore) :
    ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
    Open.IsQuasisimple L → HasDihedralSylowTwo (L ⧸ Subgroup.center L) →
    (Nat.card (Subgroup.center L)).factorization 2 ≤ 1 →
    U ≤ Subgroup.normalizer (L : Set G) → IsFourGroup U → ¬ L ≤ centralizerJoin U L →
    IsSmallDihedralSimple (L ⧸ Subgroup.center L) ∧
      U ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
  intro G _ _ L U hq hQd _ hUN hU4 hgen
  classical
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁1, hu₂1, hu₁₂, hUall⟩ := exists_fourGroup_generators hU4
  obtain ⟨⟨hUcomm⟩, hsq⟩ := hU4.1
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUcomm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set Z := Subgroup.center L with hZdef
  have hnc : ∀ u ∈ U, u ≠ 1 → ¬ ∀ x ∈ L, x * u = u * x := by
    intro u hu hu1 h
    exact hgen (fun x hx => mem_centralizerJoin_of hu hu1 hx (h x hx))
  have hne1 : ∀ u (hu : u ∈ U), u ≠ 1 → quotAutOf L (hUN hu) ≠ 1 := by
    intro u hu hu1 h
    apply hnc u hu hu1
    have h1 := conjAutOf_eq_of_quotAutOf L hq.1 (hUN hu) 1 (by
      rw [h, QuotientGroup.mk_one, map_one])
    intro x hx
    have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)
    rw [conjAutOf_apply, map_one, MulAut.one_apply] at h2
    calc x * u = u * x * u⁻¹ * u := by rw [h2]
      _ = u * x := by group
  have hu₁₂1 : u₁ * u₂ ≠ 1 := by
    intro h
    apply hu₁₂
    have h2 : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq u₂ hu₂)
    rw [← h2]
    exact eq_inv_of_mul_eq_one_left h
  set α := quotAutOf L (hUN hu₁) with hαdef
  set β := quotAutOf L (hUN hu₂) with hβdef
  have hαβ : quotAutOf L (hUN (U.mul_mem hu₁ hu₂)) = α * β := quotAutOf_mul L _ _
  have hγ : ∀ γ ∈ ({α, β, α * β} : Set (MulAut (L ⧸ Z))),
      ∃ (w : G) (hw : w ∈ U), w ≠ 1 ∧ γ = quotAutOf L (hUN hw) := by
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨u₁, hu₁, hu₁1, rfl⟩
    · exact ⟨u₂, hu₂, hu₂1, rfl⟩
    · exact ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, hu₁₂1, hαβ.symm⟩
  have hββ : ∀ (w : G) (hw : w ∈ U) (y : L), conjAutOf L (hUN hw) (conjAutOf L (hUN hw) y) = y := by
    intro w hw y
    apply Subtype.ext
    rw [conjAutOf_apply, conjAutOf_apply]
    have hw2 := hsq w hw
    calc w * (w * (y : G) * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
      _ = y := by rw [← pow_two, hw2]; group
  set C' := (centralizerJoin U L).subgroupOf L with hC'def
  set H : Subgroup (L ⧸ Z) := C'.map (QuotientGroup.mk' Z) with hHdef
  have hHne : H ≠ ⊤ := by
    intro hH
    have h1 : C' ⊔ Z = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' Z) C'
      rw [← hHdef, hH, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have h2 := eq_top_of_sup_center_eq_top hq.1 h1
    apply hgen
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ C' := h2 ▸ Subgroup.mem_top _
    exact this
  have hmemH : ∀ y : L, (y : G) ∈ centralizerJoin U L → (y : L ⧸ Z) ∈ H :=
    fun y hy => ⟨y, hy, rfl⟩
  have hinv : ∀ γ ∈ ({α, β, α * β} : Set (MulAut (L ⧸ Z))), ∀ x ∈ H, γ x ∈ H := by
    intro γ hγ' x hx
    obtain ⟨w, hw, -, rfl⟩ := hγ γ hγ'
    obtain ⟨c, hc, rfl⟩ := hx
    change quotAutOf L (hUN hw) (c : L ⧸ Z) ∈ H
    rw [quotAutOf_mk]
    apply hmemH
    rw [conjAutOf_apply]
    exact conj_mem_centralizerJoin hcomm hw (hUN hw) hc
  have hP1 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut (L ⧸ Z))), ∀ x : L ⧸ Z, γ x = x →
      Odd (orderOf x) → x ∈ H := by
    intro γ hγ' xb hfix hodd
    obtain ⟨w, hw, hw1, rfl⟩ := hγ γ hγ'
    obtain ⟨x, rfl, hxodd⟩ := exists_odd_lift Z xb hodd
    rw [quotAutOf_mk] at hfix
    have hmem : x⁻¹ * conjAutOf L (hUN hw) x ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hfix.symm
    have hcodd : Odd (orderOf (x⁻¹ * conjAutOf L (hUN hw) x)) := by
      apply Odd.of_dvd_nat hxodd
      apply orderOf_dvd_of_pow_eq_one
      set c := x⁻¹ * conjAutOf L (hUN hw) x with hcdef
      have hxc : conjAutOf L (hUN hw) x = x * c := by rw [hcdef]; group
      have hcomm' : Commute x c := (Subgroup.mem_center_iff.mp hmem) x
      have h1 : (conjAutOf L (hUN hw) x) ^ orderOf x = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [hxc, hcomm'.mul_pow, pow_orderOf_eq_one, one_mul] at h1
      exact h1
    obtain ⟨z, hz, hfz⟩ := exists_fixed_of_odd_mod_center (conjAutOf L (hUN hw))
      (hββ w hw) x hmem hcodd
    have hxz : ((x * z : L) : G) * w = w * ((x * z : L) : G) := by
      have h1 := congrArg Subtype.val hfz
      rw [conjAutOf_apply] at h1
      calc ((x * z : L) : G) * w = w * ((x * z : L) : G) * w⁻¹ * w := by rw [h1]
        _ = w * ((x * z : L) : G) := by group
    have h1 := hmemH (x * z) (mem_centralizerJoin_of hw hw1 (x * z).2 hxz)
    have h2 : ((x * z : L) : L ⧸ Z) = (x : L ⧸ Z) := by
      rw [QuotientGroup.eq]
      simpa using hz
    rwa [h2] at h1
  have hP2 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut (L ⧸ Z))), ∀ t : L ⧸ Z, t ^ 2 = 1 → t ≠ 1 →
      γ = MulAut.conj t → ∀ y : L ⧸ Z, t ∈ Subgroup.zpowers y → y ∈ H := by
    intro γ hγ' tb _ _ hconj yb hty
    obtain ⟨w, hw, hw1, rfl⟩ := hγ γ hγ'
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tb
    have hct := conjAutOf_eq_of_quotAutOf L hq.1 (hUN hw) t hconj
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hty
    have hz : (y ^ k)⁻¹ * t ∈ Z := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
      exact hk
    have hyt : y * t = t * y := by
      set z := (y ^ k)⁻¹ * t with hzdef
      have ht : t = y ^ k * z := by rw [hzdef]; group
      have hzc : ∀ g : L, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
      rw [ht]
      calc y * (y ^ k * z) = y ^ k * y * z := by group
        _ = y ^ k * (z * y) := by rw [hzc y]; group
        _ = y ^ k * z * y := by group
    have hyw : (y : G) * w = w * y := by
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hct y)
      rw [conjAutOf_apply, MulAut.conj_apply] at h1
      have h2 : t * y * t⁻¹ = y := by rw [← hyt]; group
      rw [h2] at h1
      calc (y : G) * w = w * y * w⁻¹ * w := by rw [h1]
        _ = w * y := by group
    exact hmemH y (mem_centralizerJoin_of hw hw1 y.2 hyw)
  have hcongr : ∀ (v w : G) (hv : v ∈ Subgroup.normalizer (L : Set G))
      (hw : w ∈ Subgroup.normalizer (L : Set G)), v = w → quotAutOf L hv = quotAutOf L hw := by
    intro v w hv hw hvw
    subst hvw
    rfl
  have hsqaut : ∀ (w : G) (hw : w ∈ U), quotAutOf L (hUN hw) * quotAutOf L (hUN hw) = 1 := by
    intro w hw
    rw [← quotAutOf_mul L, ← quotAutOf_one L]
    apply hcongr
    rw [← pow_two]
    exact hsq w hw
  have hα1 : α ≠ 1 := hne1 u₁ hu₁ hu₁1
  have hβ1 : β ≠ 1 := hne1 u₂ hu₂ hu₂1
  have hαβne : α ≠ β := by
    intro h
    apply hne1 (u₁ * u₂) (U.mul_mem hu₁ hu₂) hu₁₂1
    rw [hαβ, h]
    exact hsqaut u₂ hu₂
  have hαsq : α ^ 2 = 1 := by rw [pow_two]; exact hsqaut u₁ hu₁
  have hβsq : β ^ 2 = 1 := by rw [pow_two]; exact hsqaut u₂ hu₂
  have hαβc : α * β = β * α := by
    rw [hαdef, hβdef, ← quotAutOf_mul L, ← quotAutOf_mul L]
    exact hcongr _ _ _ _ (hcomm u₁ hu₁ u₂ hu₂)
  rcases hcore (L ⧸ Z) hQd α β hαβc hαsq hβsq hα1 hβ1 hαβne H hinv hP1 hP2 with
    hH | ⟨hsmall, a, b, ha, hb⟩
  · exact absurd hH hHne
  refine ⟨hsmall, ?_⟩
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have h1 := mem_sup_centralizer_of_conjAutOf L (hUN hu₁) a'
    (conjAutOf_eq_of_quotAutOf L hq.1 (hUN hu₁) a' ha)
  have h2 := mem_sup_centralizer_of_conjAutOf L (hUN hu₂) b'
    (conjAutOf_eq_of_quotAutOf L hq.1 (hUN hu₂) b' hb)
  intro u hu
  rcases hUall u hu with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact h1
  · exact h2
  · exact Subgroup.mul_mem _ h1 h2

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
