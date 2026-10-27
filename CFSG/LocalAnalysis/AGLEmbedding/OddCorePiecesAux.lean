module

public import CFSG.LocalAnalysis.AGLEmbedding.HyperplaneFixedPoint

public section

namespace CFSG.AGLEmbedding

section Index

variable {G : Type*} [Group G]

theorem sup_eq_top_of_index_eq_prime_of_not_le {p : ℕ} (hp : p.Prime) {F K : Subgroup G}
    (hF : F.index = p) (hK : ¬ K ≤ F) : F ⊔ K = ⊤ := by
  have hdvd : (F ⊔ K).index ∣ p := hF ▸ Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.index_eq_one.mp h
  · have : (F ⊔ K).FiniteIndex := ⟨by rw [h]; exact hp.ne_zero⟩
    have heq : F = F ⊔ K := Subgroup.eq_of_index_dvd_index le_sup_left (by rw [hF, h])
    exact absurd (le_sup_right.trans heq.ge) hK

theorem not_le_of_index_eq_prime {p : ℕ} (hp : p.Prime) {F F' : Subgroup G} (hF : F.index = p)
    (hF' : F'.index = p) (hne : F ≠ F') : ¬ F' ≤ F := fun hle => by
  have : F.FiniteIndex := ⟨by rw [hF]; exact hp.ne_zero⟩
  exact hne (Subgroup.eq_of_index_dvd_index hle (by rw [hF, hF'])).symm

theorem exists_mem_not_mem_of_index_eq_prime {p : ℕ} (hp : p.Prime) {F F' : Subgroup G}
    (hF : F.index = p) (hF' : F'.index = p) (hne : F ≠ F') : ∃ x ∈ F', x ∉ F :=
  IsConcreteLE.not_le_iff_exists.mp (not_le_of_index_eq_prime hp hF hF' hne)

theorem hyperplane_sup_eq_top {p : ℕ} (hp : p.Prime) {F F' : Subgroup G} (hF : F.index = p)
    (hF' : F'.index = p) (hne : F ≠ F') : F ⊔ F' = ⊤ :=
  sup_eq_top_of_index_eq_prime_of_not_le hp hF (not_le_of_index_eq_prime hp hF hF' hne)

theorem pairwise_sup_eq_top_of_index_eq_prime {p : ℕ} (hp : p.Prime) {ι : Type*}
    {F : ι → Subgroup G} (hinj : Function.Injective F) (hF : ∀ i, (F i).index = p) :
    Pairwise fun i j => F i ⊔ F j = ⊤ :=
  fun i j hij => hyperplane_sup_eq_top hp (hF i) (hF j) (hinj.ne hij)

end Index

section Independent

variable {V : Type*} [CommGroup V]

theorem card_iSup_eq_prod_of_iSupIndep {ι : Type*} [Fintype ι] {H : ι → Subgroup V}
    (hind : iSupIndep H) : Nat.card (⨆ i, H i : Subgroup V) = ∏ i, Nat.card (H i) := by
  have hcomm : Pairwise fun i j => ∀ x y : V, x ∈ H i → y ∈ H j → Commute x y :=
    fun _ _ _ x y _ _ => Commute.all x y
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), ← Nat.card_pi]
  exact Nat.card_congr
    (MonoidHom.ofInjective (Subgroup.injective_noncommPiCoprod_of_iSupIndep hind)).toEquiv.symm

theorem pow_card_le_card_closure {s : ℕ} [Fact s.Prime] (hV : IsPGroup s V) {ι : Type*}
    [Fintype ι] {H : ι → Subgroup V} (hind : iSupIndep H) {w : ι → V} (hw : ∀ i, w i ∈ H i)
    (hw1 : ∀ i, w i ≠ 1) : s ^ Fintype.card ι ≤ Nat.card (Subgroup.closure (Set.range w)) := by
  have hcl : Subgroup.closure (Set.range w) = ⨆ i, Subgroup.zpowers (w i) := by
    rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
    simp only [Subgroup.zpowers_eq_closure]
  have hind' : iSupIndep fun i => Subgroup.zpowers (w i) :=
    hind.mono fun i => Subgroup.zpowers_le.mpr (hw i)
  rw [hcl, card_iSup_eq_prod_of_iSupIndep hind', ← Finset.card_univ]
  refine Finset.pow_card_le_prod _ _ _ fun i _ => ?_
  rw [Nat.card_zpowers]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hV (w i)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hw1 i (orderOf_eq_one_iff.mp (by rw [hk, pow_zero]))
  rw [hk]
  exact Nat.le_self_pow hk0 s

end Independent

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

@[expose] def actCommutator (U : Subgroup V) (F : Subgroup A) : Subgroup V :=
  Subgroup.closure {w | ∃ u ∈ U, ∃ a ∈ F, (a • u) * u⁻¹ = w}

@[expose] def fixedPiece (F : Subgroup A) : Subgroup V :=
  actCommutator (fixedBy F) (⊤ : Subgroup A)

theorem mem_actCommutator {U : Subgroup V} {F : Subgroup A} {u : V} (hu : u ∈ U) {a : A}
    (ha : a ∈ F) : (a • u) * u⁻¹ ∈ actCommutator U F :=
  Subgroup.subset_closure ⟨u, hu, a, ha, rfl⟩

theorem actCommutator_le {U : Subgroup V} {F : Subgroup A} {K : Subgroup V}
    (h : ∀ u ∈ U, ∀ a ∈ F, (a • u) * u⁻¹ ∈ K) : actCommutator U F ≤ K := by
  rw [actCommutator, Subgroup.closure_le]
  rintro _ ⟨u, hu, a, ha, rfl⟩
  exact h u hu a ha

theorem actCommutator_mono {U U' : Subgroup V} {F F' : Subgroup A} (hU : U ≤ U')
    (hF : F ≤ F') : actCommutator U F ≤ actCommutator U' F' :=
  actCommutator_le fun _ hu _ ha => mem_actCommutator (hU hu) (hF ha)

theorem smul_mem_fixedBy {F : Subgroup A} {v : V} (hv : v ∈ (fixedBy F : Subgroup V)) (a : A) :
    a • v ∈ (fixedBy F : Subgroup V) := fun b hb => by
  rw [← mul_smul, mul_comm b a, mul_smul, hv b hb]

theorem smul_smul_mul_inv (a b : A) (u : V) :
    a • ((b • u) * u⁻¹) = (b • (a • u)) * (a • u)⁻¹ := by
  rw [smul_mul', smul_inv', ← mul_smul, mul_comm a b, mul_smul]

theorem smul_mem_actCommutator {U : Subgroup V} (hU : ∀ a : A, ∀ u ∈ U, a • u ∈ U)
    {F : Subgroup A} (a : A) {w : V} (hw : w ∈ actCommutator U F) :
    a • w ∈ actCommutator U F := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨u, hu, b, hb, rfl⟩ := hw
    rw [smul_smul_mul_inv]
    exact mem_actCommutator (hU a u hu) hb
  | one => rw [smul_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [smul_mul']; exact mul_mem hx hy
  | inv x _ hx => rw [smul_inv']; exact inv_mem hx

theorem smul_mem_fixedPiece {F : Subgroup A} (a : A) {w : V}
    (hw : w ∈ (fixedPiece F : Subgroup V)) : a • w ∈ (fixedPiece F : Subgroup V) :=
  smul_mem_actCommutator (fun a _ hu => smul_mem_fixedBy hu a) a hw

theorem fixedPiece_le_fixedBy (F : Subgroup A) :
    (fixedPiece F : Subgroup V) ≤ fixedBy F :=
  actCommutator_le fun _ hu a _ => mul_mem (smul_mem_fixedBy hu a) (inv_mem hu)

theorem fixedPiece_eq_bot_iff {F : Subgroup A} :
    (fixedPiece F : Subgroup V) = ⊥ ↔ (fixedBy F : Subgroup V) ≤ fixedBy (⊤ : Subgroup A) := by
  constructor
  · intro h v hv a _
    have hmem := mem_actCommutator (hv : v ∈ (fixedBy F : Subgroup V)) (Subgroup.mem_top a)
    rw [← fixedPiece, h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  · intro h
    rw [eq_bot_iff]
    refine actCommutator_le fun u hu a _ => ?_
    rw [h hu a (Subgroup.mem_top a), mul_inv_cancel]
    exact one_mem _

theorem fixedPiece_le_actCommutator {F F' : Subgroup A} (h : F ⊔ F' = ⊤) :
    (fixedPiece F : Subgroup V) ≤ actCommutator (⊤ : Subgroup V) F' :=
  actCommutator_le fun u hu a _ => by
    have ha : a ∈ F ⊔ F' := h ▸ Subgroup.mem_top a
    obtain ⟨b, hb, b', hb', rfl⟩ := Subgroup.mem_sup.mp ha
    rw [mul_comm b b', mul_smul, hu b hb]
    exact mem_actCommutator (Subgroup.mem_top u) hb'

variable [Finite A]

theorem actCommutator_top_inf_fixedBy {F : Subgroup A}
    (hcop : Nat.Coprime (Nat.card F) (Nat.card V)) :
    actCommutator (⊤ : Subgroup V) F ⊓ (fixedBy F : Subgroup V) = ⊥ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let σ : V →* V :=
    { toFun := fun v => ∏ b : F, (b : A) • v
      map_one' := by simp
      map_mul' := fun v w => by simp [smul_mul', Finset.prod_mul_distrib] }
  have hσ : ∀ v, σ v = ∏ b : F, (b : A) • v := fun _ => rfl
  have hσsmul : ∀ v : V, ∀ b ∈ F, σ (b • v) = σ v := fun v b hb => by
    rw [hσ, hσ]
    exact Fintype.prod_equiv (Equiv.mulRight (⟨b, hb⟩ : F)) _ _ fun c => by
      rw [Equiv.coe_mulRight, Subgroup.coe_mul, mul_smul]
  have hle : actCommutator (⊤ : Subgroup V) F ≤ σ.ker := actCommutator_le fun v _ b hb => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσsmul v b hb, mul_inv_cancel]
  rw [eq_bot_iff]
  rintro v ⟨hvD, hvC⟩
  have h1 : v ^ Fintype.card F = 1 := by
    have hv := hle hvD
    rw [MonoidHom.mem_ker, hσ, Finset.prod_congr rfl fun (b : F) _ => hvC (b : A) b.2,
      Finset.prod_const, Finset.card_univ] at hv
    exact hv
  have h2 : v ^ Nat.card V = 1 := pow_card_eq_one'
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [← Nat.card_eq_fintype_card, hcop.gcd_eq_one, pow_one] at h3
  exact h3

theorem iSupIndep_fixedPiece {ι : Type*} {F : ι → Subgroup A}
    (hF : Pairwise fun i j => F i ⊔ F j = ⊤) (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) :
    iSupIndep fun i => (fixedPiece (F i) : Subgroup V) := by
  rw [iSupIndep_def]
  intro i
  have h1 : (⨆ j, ⨆ (_ : j ≠ i), (fixedPiece (F j) : Subgroup V)) ≤
      actCommutator (⊤ : Subgroup V) (F i) :=
    iSup₂_le fun j hj => fixedPiece_le_actCommutator (hF hj)
  have hcopi : Nat.Coprime (Nat.card (F i)) (Nat.card V) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card (F i)) hcop
  rw [disjoint_iff, eq_bot_iff, ← actCommutator_top_inf_fixedBy hcopi, inf_comm]
  exact inf_le_inf h1 (fixedPiece_le_fixedBy (F i))

theorem pow_card_le_card_closure_of_fixedPiece {s p : ℕ} [Fact s.Prime] (hp : p.Prime)
    (hV : IsPGroup s V) (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) {ι : Type*} [Fintype ι]
    {F : ι → Subgroup A} (hinj : Function.Injective F) (hF : ∀ i, (F i).index = p) {w : ι → V}
    (hw : ∀ i, w i ∈ (fixedPiece (F i) : Subgroup V)) (hw1 : ∀ i, w i ≠ 1) :
    s ^ Fintype.card ι ≤ Nat.card (Subgroup.closure (Set.range w)) :=
  pow_card_le_card_closure hV
    (iSupIndep_fixedPiece (pairwise_sup_eq_top_of_index_eq_prime hp hinj hF) hcop) hw hw1

variable [Finite V]

theorem pow_card_le_card_of_fixedPiece_ne_bot {s p : ℕ} [Fact s.Prime] (hp : p.Prime)
    (hV : IsPGroup s V) (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) {ι : Type*} [Fintype ι]
    {F : ι → Subgroup A} (hinj : Function.Injective F) (hF : ∀ i, (F i).index = p)
    (hne : ∀ i, (fixedPiece (F i) : Subgroup V) ≠ ⊥) : s ^ Fintype.card ι ≤ Nat.card V := by
  choose w hw hw1 using fun i => (Subgroup.bot_or_exists_ne_one (fixedPiece (F i) :
    Subgroup V)).resolve_left (hne i)
  exact (pow_card_le_card_closure_of_fixedPiece hp hV hcop hinj hF hw hw1).trans
    (Subgroup.card_le_card_group _)

end CFSG.AGLEmbedding
