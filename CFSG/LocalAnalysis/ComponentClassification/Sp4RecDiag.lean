module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog71Cover

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem ker_mk_comp_subtype {K : Subgroup X} (hK : K.IsSubnormal) :
    ((QuotientGroup.mk' (pPrimeCore 2 X)).comp K.subtype).ker = pPrimeCore 2 K := by
  have h := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hK
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hk
    have hk' : (k : X) ∈ (pPrimeCore 2 K).map K.subtype := h ▸ mem_inf.mpr ⟨k.2, hk⟩
    obtain ⟨k', hk', hkk'⟩ := hk'
    rwa [show k' = k from Subtype.ext hkk'] at hk'
  · intro hk
    have hk' : (k : X) ∈ K ⊓ pPrimeCore 2 X := h ▸ ⟨k, hk, rfl⟩
    exact (mem_inf.mp hk').2

@[expose] def quotientEquivMap {K : Subgroup X} (hK : K.IsSubnormal) :
    K ⧸ pPrimeCore 2 K ≃* ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 X))) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk_comp_subtype hK).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))

theorem quotientEquivMap_apply {K : Subgroup X} (hK : K.IsSubnormal) (k : K) :
    ((quotientEquivMap hK (k : K ⧸ pPrimeCore 2 K) : ↥(K.map _)) : X ⧸ pPrimeCore 2 X) =
      QuotientGroup.mk' (pPrimeCore 2 X) (k : X) :=
  rfl

theorem commute_map_of_ne {K L : Subgroup X} (hK : IsPComponent 2 K) (hL : IsPComponent 2 L)
    (hne : K ≠ L) {k l : X} (hk : k ∈ K) (hl : l ∈ L) :
    QuotientGroup.mk' (pPrimeCore 2 X) k * QuotientGroup.mk' (pPrimeCore 2 X) l =
      QuotientGroup.mk' (pPrimeCore 2 X) l * QuotientGroup.mk' (pPrimeCore 2 X) k := by
  obtain ⟨-, -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two K L hK hL).2 hne
  obtain ⟨-, -, hs, -, -⟩ := id hK
  have hcO : ⁅K, L⁆ ≤ pPrimeCore 2 X := by
    refine hc.trans (inf_le_left.trans ?_)
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  have hmem : ⁅k, l⁆ ∈ pPrimeCore 2 X := hcO (commutator_mem_commutator hk hl)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 X) ⁅k, l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1


theorem exists_mem_centralizer_of_mk {t : X} (ht : t * t = 1) {d : X ⧸ pPrimeCore 2 X}
    (hd : QuotientGroup.mk' (pPrimeCore 2 X) t * d * (QuotientGroup.mk' (pPrimeCore 2 X) t)⁻¹ =
      d) :
    ∃ x ∈ centralizer ({t} : Set X), QuotientGroup.mk' (pPrimeCore 2 X) x = d := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 X)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 (pPrimeCore_coprime_card (p := 2)))
  obtain ⟨x, hx, hfix⟩ := OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel
    (MulAut.conj t) (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 X) t))
    (fun y => by simp [MulAut.conj_apply, ← mul_assoc, ht, htinv, mul_assoc y t t])
    (QuotientGroup.mk' (pPrimeCore 2 X)) (QuotientGroup.mk'_surjective _) hodd
    (fun y => by simp [MulAut.conj_apply]) d (by simpa [MulAut.conj_apply] using hd)
  refine ⟨x, ?_, hx⟩
  rw [mem_centralizer_singleton_iff]
  have h1 : t * x * t⁻¹ = x := by simpa [MulAut.conj_apply] using hfix
  calc x * t = t * x * t⁻¹ * t := by rw [h1]
    _ = t * x := by group

theorem mem_conjugate_iff {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

omit [Finite X] in
theorem mem_sup_iff_of_commute {A C : Subgroup X} (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    {y : X} : y ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = y := by
  have hc : ∀ (a : A) (c : C), Commute (A.subtype a) (C.subtype c) := fun a c => hcomm a a.2 c c.2
  have hrange := MonoidHom.noncommCoprod_range A.subtype C.subtype hc
  rw [range_subtype, range_subtype] at hrange
  rw [← hrange]
  constructor
  · rintro ⟨⟨a, c⟩, rfl⟩
    exact ⟨a, a.2, c, c.2, rfl⟩
  · rintro ⟨a, ha, c, hc', rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨c, hc'⟩), rfl⟩

section Diagonal

variable {a b : X} {K : Subgroup X}

@[expose] def diag (A : X ⧸ pPrimeCore 2 X) (Kb : Subgroup (X ⧸ pPrimeCore 2 X))
    (hcomm : ∀ u ∈ Kb, ∀ v ∈ Kb, v * (A⁻¹ * u * A) = (A⁻¹ * u * A) * v) :
    ↥Kb →* X ⧸ pPrimeCore 2 X where
  toFun u := (u : X ⧸ pPrimeCore 2 X) * (A⁻¹ * u * A)
  map_one' := by simp
  map_mul' u v := by
    simp only [coe_mul]
    have h := hcomm u u.2 v v.2
    calc (u : X ⧸ pPrimeCore 2 X) * v * (A⁻¹ * (u * v) * A)
        = u * (v * (A⁻¹ * u * A)) * (A⁻¹ * v * A) := by group
      _ = u * ((A⁻¹ * u * A) * v) * (A⁻¹ * v * A) := by rw [h]
      _ = u * (A⁻¹ * u * A) * (v * (A⁻¹ * v * A)) := by group

theorem diag_facts (ha : a * a = 1) (hb : orderOf b = 2) (hbZ : b ∈ center X)
    (hK : IsPComponent 2 K) (hKa : conjugate K a ≠ K) (hbK : b ∈ K)
    (hZK : Nat.card (center (K ⧸ pPrimeCore 2 K)) = 2) :
    ∃ (D : Subgroup (X ⧸ pPrimeCore 2 X)) (_ : D ≃* K ⧸ Open.fusionZStar K),
      IsSimpleGroup D ∧
      (∀ d ∈ D, QuotientGroup.mk' (pPrimeCore 2 X) a * d *
        (QuotientGroup.mk' (pPrimeCore 2 X) a)⁻¹ = d) ∧
      ∀ x ∈ K ⊔ conjugate K a, x ∈ centralizer ({a} : Set X) →
        ∃ d ∈ D, QuotientGroup.mk' (pPrimeCore 2 X) x = d ∨
          QuotientGroup.mk' (pPrimeCore 2 X) x = d * QuotientGroup.mk' (pPrimeCore 2 X) b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set A := π a with hA
  have hA2 : A * A = 1 := by rw [hA, ← map_mul, ha, map_one]
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbb : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rwa [hb, pow_two] at h
  set K' := conjugate K a with hK'
  have hK'pc : IsPComponent 2 K' := UnbalancedLayer.isPComponent_conjugate hK a
  set Kb := K.map π with hKb
  set Kab := K'.map π with hKab
  have hcomm : ∀ u ∈ Kb, ∀ v ∈ Kab, u * v = v * u := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    exact commute_map_of_ne hK hK'pc (Ne.symm hKa) hk hk'
  have hconj : ∀ u ∈ Kb, A⁻¹ * u * A ∈ Kab := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨a⁻¹ * k * a, mem_conjugate_iff.mpr ?_, by simp [hA]⟩
    simpa [mul_assoc] using hk
  have hconj' : ∀ v ∈ Kab, A⁻¹ * v * A ∈ Kb := by
    rintro _ ⟨k', hk', rfl⟩
    refine ⟨a⁻¹ * k' * a, ?_, by simp [hA]⟩
    have h1 := mem_conjugate_iff.mp hk'
    rw [hainv] at h1 ⊢
    simpa [mul_assoc, ← mul_assoc a a, ha] using h1
  obtain ⟨-, -, hKs, -, -⟩ := id hK
  set eK := quotientEquivMap hKs with heK
  have hZKb : Nat.card (center Kb) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr eK).symm.toEquiv).trans hZK
  have hbKb : π b ∈ Kb := ⟨b, hbK, rfl⟩
  have hbc : ∀ y, π b * y = y * π b := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hbZ y).symm]
  have hb1 : π b ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    rw [hb] at h2
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 (pPrimeCore_coprime_card (p := 2))
  have hbcen : (⟨π b, hbKb⟩ : Kb) ∈ center Kb :=
    mem_center_iff.mpr fun g => Subtype.ext (hbc g).symm
  have hcen : ∀ z ∈ center Kb, (z : X ⧸ pPrimeCore 2 X) = 1 ∨ (z : X ⧸ pPrimeCore 2 X) = π b := by
    intro z hz
    obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp hZKb
    have hmem : ∀ w : center Kb, w = x ∨ w = y := fun w => by
      have : w ∈ ({x, y} : Set (center Kb)) := hset ▸ Set.mem_univ w
      simpa using this
    have hne1 : (1 : center Kb) ≠ ⟨⟨π b, hbKb⟩, hbcen⟩ := fun h =>
      hb1 (congrArg (fun w : center Kb => ((w : Kb) : X ⧸ pPrimeCore 2 X)) h).symm
    have key : ∀ w : center Kb, w = 1 ∨ w = ⟨⟨π b, hbKb⟩, hbcen⟩ := by
      intro w
      rcases hmem 1 with h1 | h1 <;> rcases hmem ⟨⟨π b, hbKb⟩, hbcen⟩ with h2 | h2 <;>
        rcases hmem w with h3 | h3
      all_goals first
        | exact absurd (h1.trans h2.symm) hne1
        | exact Or.inl (h3.trans h1.symm)
        | exact Or.inr (h3.trans h2.symm)
    rcases key ⟨z, hz⟩ with h | h
    · left
      exact congrArg (fun w : center Kb => ((w : Kb) : X ⧸ pPrimeCore 2 X)) h
    · right
      exact congrArg (fun w : center Kb => ((w : Kb) : X ⧸ pPrimeCore 2 X)) h
  have hint : ∀ y ∈ Kb, y ∈ Kab → y = 1 ∨ y = π b := by
    intro y hy hy'
    exact hcen ⟨y, hy⟩ (mem_center_iff.mpr fun g => Subtype.ext (hcomm g g.2 y hy')) 
  have hcomm' : ∀ u ∈ Kb, ∀ v ∈ Kb, v * (A⁻¹ * u * A) = (A⁻¹ * u * A) * v :=
    fun u hu v hv => hcomm v hv _ (hconj u hu)
  set δ := diag A Kb hcomm' with hδ
  have hδapp : ∀ u : Kb, δ u = (u : X ⧸ pPrimeCore 2 X) * (A⁻¹ * u * A) := fun u => rfl
  have hker : δ.ker = center Kb := by
    ext u
    rw [MonoidHom.mem_ker, hδapp]
    constructor
    · intro h1
      have hu : (u : X ⧸ pPrimeCore 2 X) = (A⁻¹ * u * A)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hu' : (u : X ⧸ pPrimeCore 2 X) ∈ Kab := hu ▸ inv_mem (hconj u u.2)
      exact mem_center_iff.mpr fun g => Subtype.ext (hcomm g g.2 u hu')
    · intro hz
      rcases hcen u hz with h1 | h1 <;> rw [h1]
      · group
      · have h2 : A⁻¹ * π b * A = π b := by
          rw [← hbc A⁻¹, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2, ← map_mul, hbb, map_one]
  set e2 : δ.range ≃* (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) :=
    (QuotientGroup.quotientKerEquivRange δ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.congr (center Kb) (center (K ⧸ pPrimeCore 2 K)) eK.symm
          (Subgroup.map_center_eq eK.symm))) with he2
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple
    2 K).1 hK
  have : IsSimpleGroup ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := hq.2.1
  refine ⟨δ.range, e2.trans (GSThmB.oddBarCenterEquiv K), e2.isSimpleGroup, ?_, ?_⟩
  ·
    rintro _ ⟨u, rfl⟩
    rw [hδapp]
    have h1 := hcomm u u.2 _ (hconj u u.2)
    calc A * (u * (A⁻¹ * u * A)) * A⁻¹ = A * (A⁻¹ * u * A * u) * A⁻¹ := by rw [h1]
      _ = u * (A * u * A⁻¹) := by group
      _ = u * (A⁻¹ * u * A) := by rw [hAinv]
  ·
    intro x hx hxa
    have hxπ : π x ∈ Kb ⊔ Kab := by
      have := mem_map_of_mem π hx
      rwa [Subgroup.map_sup] at this
    obtain ⟨u, hu, v, hv, huv⟩ := (mem_sup_iff_of_commute hcomm).mp hxπ
    set w := A⁻¹ * v * A with hw
    have hwK : w ∈ Kb := hconj' v hv
    have hAA' : A⁻¹ * A⁻¹ = 1 := by rw [hAinv, hA2]
    have hvw : v = A⁻¹ * w * A := by
      calc v = (A⁻¹ * A⁻¹) * v * (A * A) := by rw [hAA', hA2, one_mul, mul_one]
        _ = A⁻¹ * w * A := by rw [hw]; group
    have hfix : A⁻¹ * π x * A = π x := by
      have h1 : a * x = x * a := (mem_centralizer_singleton_iff.mp hxa).symm
      rw [hA, ← map_inv, ← map_mul, ← map_mul, hainv, h1, mul_assoc, ha, mul_one]
    have hc : u⁻¹ * w ∈ Kab := by
      have h1 : A⁻¹ * u * A * w = u * v := by
        rw [← huv] at hfix
        calc A⁻¹ * u * A * w = A⁻¹ * (u * v) * A := by rw [hw]; group
          _ = u * v := hfix
      have h2 : u⁻¹ * w = v * (A⁻¹ * u * A)⁻¹ := by
        have h3 := hcomm w hwK _ (hconj u hu)
        calc u⁻¹ * w = u⁻¹ * (A⁻¹ * u * A * w) * (A⁻¹ * u * A)⁻¹ := by
              rw [← h3]; group
          _ = v * (A⁻¹ * u * A)⁻¹ := by rw [h1]; group
      rw [h2]
      exact mul_mem hv (inv_mem (hconj u hu))
    have hcK : u⁻¹ * w ∈ Kb := mul_mem (inv_mem hu) hwK
    refine ⟨δ ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, ?_⟩
    rcases hint _ hcK hc with h1 | h1
    · left
      have hwu : w = u := by
        calc w = u * (u⁻¹ * w) := by group
          _ = u := by rw [h1, mul_one]
      calc π x = u * v := huv.symm
        _ = u * (A⁻¹ * u * A) := by rw [hvw, hwu]
        _ = δ ⟨u, hu⟩ := (hδapp ⟨u, hu⟩).symm
    · right
      have hwu : w = u * π b := by
        calc w = u * (u⁻¹ * w) := by group
          _ = u * π b := by rw [h1]
      have h2 : A⁻¹ * (u * π b) * A = A⁻¹ * u * A * π b := by
        calc A⁻¹ * (u * π b) * A = A⁻¹ * u * (π b * A) := by group
          _ = A⁻¹ * u * (A * π b) := by rw [hbc A]
          _ = A⁻¹ * u * A * π b := by group
      calc π x = u * v := huv.symm
        _ = u * (A⁻¹ * (u * π b) * A) := by rw [hvw, hwu]
        _ = u * (A⁻¹ * u * A) * π b := by rw [h2]; group
        _ = δ ⟨u, hu⟩ * π b := by rw [hδapp]

omit [Finite X] in
theorem commutator_sup_le_of_le_center {D Z : Subgroup X} (hZ : Z ≤ center X) :
    ⁅D ⊔ Z, D ⊔ Z⁆ ≤ D := by
  have hcomm : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d := fun d _ z hz =>
    (mem_center_iff.mp (hZ hz) d)
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hg₁
  obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hg₂
  have c₁ := mem_center_iff.mp (hZ hz₁)
  have c₂ := mem_center_iff.mp (hZ hz₂)
  have e1 : z₁ * (d₂ * z₂) * z₁⁻¹ = d₂ * z₂ := by
    rw [← c₁ (d₂ * z₂), mul_assoc, mul_inv_cancel, mul_one]
  have h : ⁅d₁ * z₁, d₂ * z₂⁆ = ⁅d₁, d₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc d₁ * z₁ * (d₂ * z₂) * (d₁ * z₁)⁻¹ * (d₂ * z₂)⁻¹
        = d₁ * (z₁ * (d₂ * z₂) * z₁⁻¹) * d₁⁻¹ * (d₂ * z₂)⁻¹ := by group
      _ = d₁ * (d₂ * z₂) * d₁⁻¹ * (d₂ * z₂)⁻¹ := by rw [e1]
      _ = d₁ * d₂ * (z₂ * d₁⁻¹) * z₂⁻¹ * d₂⁻¹ := by group
      _ = d₁ * d₂ * (d₁⁻¹ * z₂) * z₂⁻¹ * d₂⁻¹ := by rw [← c₂ d₁⁻¹]
      _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by group
  rw [h, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)

theorem two_dvd_card_of_isQuasisimple {L : Type*} [Group L] [Finite L]
    (hq : IsQuasisimple (L ⧸ pPrimeCore 2 L)) : 2 ∣ Nat.card L := by
  by_contra hodd
  have htop : pPrimeCore 2 L = ⊤ := by
    refine eq_top_iff.mpr (le_sSup ⟨inferInstance, ?_⟩)
    rw [card_top]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr hodd
  have h1 : ∀ w : L, (w : L ⧸ pPrimeCore 2 L) = 1 := fun w =>
    (QuotientGroup.eq_one_iff w).mpr (htop ▸ mem_top w)
  obtain ⟨-, -, u, v, huv⟩ := hq
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  rw [h1 u, h1 v] at huv
  exact huv rfl

theorem nonempty_quotient_equiv_of_diag (ha : a * a = 1) (hb : orderOf b = 2)
    (hbZ : b ∈ center X) (hK : IsPComponent 2 K) (hKa : conjugate K a ≠ K) (hbK : b ∈ K)
    (hZK : Nat.card (center (K ⧸ pPrimeCore 2 K)) = 2) {JB : Subgroup X}
    (hJBV : JB ≤ K ⊔ conjugate K a) (hJBa : JB ≤ centralizer ({a} : Set X))
    (hJB : IsPComponent 2 (JB.subgroupOf (centralizer ({a} : Set X)))) :
    Nonempty (JB ⧸ pPrimeCore 2 JB ≃* K ⧸ Open.fusionZStar K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, eD, hDs, hDfix, hfixD⟩ := diag_facts ha hb hbZ hK hKa hbK hZK
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set C := centralizer ({a} : Set X) with hC
  obtain ⟨hJBs, -, hJBq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 hJB
  have hJBq' : IsQuasisimple (JB ⧸ pPrimeCore 2 JB) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (subgroupOfEquivOfLe hJBa))).1 hJBq
  have : Group.IsPerfect (JB.subgroupOf C) := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJB
  have : Group.IsPerfect JB := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hJBa).toMonoidHom) (subgroupOfEquivOfLe hJBa).surjective
  have hperf : ⁅JB, JB⁆ = JB := by
    have h1 : (commutator JB).map JB.subtype = JB := by
      rw [Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      range_subtype] at h1
    exact h1
  have hbc : π b ∈ center (X ⧸ pPrimeCore 2 X) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hbZ y)]
  have hZc : zpowers (π b) ≤ center (X ⧸ pPrimeCore 2 X) := zpowers_le.mpr hbc
  have hJD : JB.map π ≤ D := by
    have h1 : JB.map π ≤ D ⊔ zpowers (π b) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨d, hd, h | h⟩ := hfixD x (hJBV hx) (hJBa hx)
      · rw [h]; exact mem_sup_left hd
      · rw [h]; exact mul_mem (mem_sup_left hd) (mem_sup_right (mem_zpowers _))
    calc JB.map π = ⁅JB, JB⁆.map π := by rw [hperf]
      _ = ⁅JB.map π, JB.map π⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅D ⊔ zpowers (π b), D ⊔ zpowers (π b)⁆ := commutator_mono h1 h1
      _ ≤ D := commutator_sup_le_of_le_center hZc
  have hDC : D ≤ C.map π := by
    intro d hd
    obtain ⟨x, hx, hxd⟩ := exists_mem_centralizer_of_mk ha (hDfix d hd)
    exact ⟨x, hx, hxd⟩
  have hsub : ((JB.map π).subgroupOf D).IsSubnormal := by
    have h1 : ((JB.subgroupOf C).map (π.subgroupMap C)).IsSubnormal :=
      hJBs.map (π.subgroupMap_surjective C)
    have h2 : (((JB.subgroupOf C).map (π.subgroupMap C)).comap
        (Subgroup.inclusion hDC)).IsSubnormal := h1.comap _
    convert h2 using 1
    ext ⟨d, hd⟩
    simp only [mem_subgroupOf, mem_comap, mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hJBa hx⟩, hx, rfl⟩
    · rintro ⟨⟨x, hxC⟩, hx, hxd⟩
      refine ⟨x, hx, ?_⟩
      have := congrArg Subtype.val hxd
      simpa using this
  have hJBeq : JB.map π = D := by
    rcases hsub.eq_bot_or_top_of_isSimpleGroup hDs with h | h
    · exfalso
      have hbot : JB.map π = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have : (⟨y, hJD hy⟩ : D) ∈ (JB.map π).subgroupOf D := hy
        rw [h, mem_bot] at this
        exact congrArg Subtype.val this
      have hJBO : JB ≤ pPrimeCore 2 X := by
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 X), ← Subgroup.map_eq_bot_iff]
        exact hbot
      have h2 : 2 ∣ Nat.card JB := two_dvd_card_of_isQuasisimple hJBq'
      exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
        (h2.trans (Subgroup.card_dvd_of_le hJBO)) (pPrimeCore_coprime_card (p := 2))
    · refine le_antisymm hJD fun d hd => ?_
      have : (⟨d, hd⟩ : D) ∈ (JB.map π).subgroupOf D := h ▸ mem_top _
      exact this
  set φ : JB →* X ⧸ pPrimeCore 2 X := π.comp JB.subtype with hφ
  have hrange : φ.range = D := by rw [hφ, MonoidHom.range_comp, range_subtype, hJBeq]
  have hkerle : φ.ker ≤ pPrimeCore 2 JB := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have hle : (φ.ker).map JB.subtype ≤ pPrimeCore 2 X := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' := MonoidHom.mem_ker.mp hk
      rw [hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hk'
      exact hk'
    have hdvd : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 X) := by
      rw [← Nat.card_congr ((φ.ker).equivMapOfInjective _ JB.subtype_injective).toEquiv.symm]
      exact Subgroup.card_dvd_of_le hle
    exact Nat.Coprime.coprime_dvd_right hdvd (pPrimeCore_coprime_card (p := 2))
  have hkerge : pPrimeCore 2 JB ≤ φ.ker := by
    have hsimpR : IsSimpleGroup φ.range := hrange ▸ hDs
    have hMn : ((pPrimeCore 2 JB).map φ.rangeRestrict).Normal :=
      Subgroup.Normal.map inferInstance _ φ.rangeRestrict_surjective
    rcases hMn.eq_bot_or_eq_top with h | h
    · intro m hm
      have h1 : φ.rangeRestrict m ∈ (pPrimeCore 2 JB).map φ.rangeRestrict := mem_map_of_mem _ hm
      rw [h, mem_bot] at h1
      rw [MonoidHom.mem_ker]
      have h2 := congrArg Subtype.val h1
      simpa using h2
    · exfalso
      have hMtop : pPrimeCore 2 JB = ⊤ := by
        rw [eq_top_iff]
        intro j _
        have h1 : φ.rangeRestrict j ∈ (pPrimeCore 2 JB).map φ.rangeRestrict := h ▸ mem_top _
        obtain ⟨m, hm, hmj⟩ := h1
        have hmj' : φ m = φ j := congrArg Subtype.val hmj
        have hk : m⁻¹ * j ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hmj', inv_mul_cancel]
        have h2 : j = m * (m⁻¹ * j) := by group
        rw [h2]
        exact mul_mem hm (hkerle hk)
      have h1 : ∀ w : JB, (w : JB ⧸ pPrimeCore 2 JB) = 1 := fun w =>
        (QuotientGroup.eq_one_iff w).mpr (hMtop ▸ mem_top w)
      obtain ⟨-, -, u, v, huv⟩ := hJBq'
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      rw [h1 u, h1 v] at huv
      exact huv rfl
  have hker : φ.ker = pPrimeCore 2 JB := le_antisymm hkerle hkerge
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans ((MulEquiv.subgroupCongr hrange).trans eD))⟩

end Diagonal

@[expose] def zStarQuotientCongr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') :
    Y ⧸ Open.fusionZStar Y ≃* Y' ⧸ Open.fusionZStar Y' :=
  (GSThmB.oddBarCenterEquiv Y).symm.trans
    ((QuotientGroup.congr _ _ (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e)
      (Subgroup.map_center_eq _)).trans (GSThmB.oddBarCenterEquiv Y'))

theorem nonempty_quotient_equiv_of_diag_in {H : Type*} [Group H] [Finite H] {a b : H}
    (ha : a * a = 1) (hb : orderOf b = 2) (hab : a * b = b * a) {K JB : Subgroup H}
    (hKW : K ≤ centralizer ({b} : Set H))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))))
    (hKa : conjugate K a ≠ K) (hbK : b ∈ K) (hZK : Nat.card (center (K ⧸ pPrimeCore 2 K)) = 2)
    (hJBV : JB ≤ K ⊔ conjugate K a) (hJBa : JB ≤ centralizer ({a} : Set H))
    (hJB : IsPComponent 2
      (JB.subgroupOf (centralizer ({a} : Set H) ⊓ centralizer ({b} : Set H)))) :
    Nonempty (JB ⧸ pPrimeCore 2 JB ≃* K ⧸ Open.fusionZStar K) := by
  classical
  set W := centralizer ({b} : Set H) with hW
  have haW : a ∈ W := mem_centralizer_singleton_iff.mpr hab
  have hbW : b ∈ W := mem_centralizer_singleton_iff.mpr rfl
  have hKaW : conjugate K a ≤ W := by
    intro x hx
    have h1 := hKW (mem_conjugate_iff.mp hx)
    have h2 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem haW) h1) haW
  have hJBW : JB ≤ W := hJBV.trans (sup_le hKW hKaW)
  set a' : W := ⟨a, haW⟩ with ha'
  set b' : W := ⟨b, hbW⟩ with hb'
  have hconjW : conjugate (K.subgroupOf W) a' = (conjugate K a).subgroupOf W := by
    ext x
    rw [mem_conjugate_iff, mem_subgroupOf, mem_subgroupOf, mem_conjugate_iff]
    rfl
  have hcentW : centralizer ({a'} : Set W) = (centralizer ({a} : Set H) ⊓ W).subgroupOf W := by
    ext x
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨congrArg Subtype.val h, x.2⟩
    · rintro ⟨h, -⟩
      exact Subtype.ext h
  have hKK : K.subgroupOf W ≃* K := subgroupOfEquivOfLe hKW
  have hJJ : JB.subgroupOf W ≃* JB := subgroupOfEquivOfLe hJBW
  obtain ⟨e⟩ := nonempty_quotient_equiv_of_diag (X := W) (a := a') (b := b') (K := K.subgroupOf W)
    (Subtype.ext ha) (by rw [hb', ← Subgroup.orderOf_coe]; exact hb)
    (mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)) hK
    (by
      rw [hconjW]
      intro h
      have h1 := subgroupOf_inj.mp h
      rw [inf_of_le_left hKaW, inf_of_le_left hKW] at h1
      exact hKa h1)
    (mem_subgroupOf.mpr hbK)
    ((Nat.card_congr (Subgroup.centerCongr
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 hKK)).toEquiv).trans hZK)
    (JB := JB.subgroupOf W)
    (by
      rw [hconjW, ← subgroupOf_sup hKW hKaW]
      exact fun x hx => mem_subgroupOf.mpr (hJBV (mem_subgroupOf.mp hx)))
    (fun x hx => mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hJBa (mem_subgroupOf.mp hx)))))
    (by
      rw [hcentW]
      exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
        Nat.prime_two).mpr hJB)
  exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 hJJ).symm.trans
    (e.trans (zStarQuotientCongr hKK))⟩

end CFSG.ComponentClassification.Sp4Rec
