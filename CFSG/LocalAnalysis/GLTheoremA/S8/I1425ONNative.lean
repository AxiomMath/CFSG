module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentON
public import CFSG.LocalAnalysis.GLTheoremA.S8.ONFacts

public section


namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

section Spread

open Finset


theorem exists_plane_le {S : Type*} [Group S] [Finite S] (hS : Nat.card S = 81)
    (D : S → Subgroup S) (hmem : ∀ s, s ≠ 1 → s ∈ D s) (hcard : ∀ s, s ≠ 1 → Nat.card (D s) = 9)
    (hconst : ∀ s, s ≠ 1 → ∀ t ∈ D s, t ≠ 1 → D t = D s) {F : Subgroup S}
    (hF : Nat.card F = 27) : ∃ s, s ≠ 1 ∧ D s ≤ F := by
  classical
  have : Fintype S := Fintype.ofFinite S
  set Sh : Finset S := univ.filter (· ≠ 1) with hSh
  set Ps : Finset (Subgroup S) := Sh.image D with hPs
  have hSh80 : Sh.card = 80 := by
    have h1 : Sh = univ.erase 1 := by
      ext x; simp [Sh]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hS]
  have hfib : ∀ P ∈ Ps, Sh.filter (fun a => D a = P) = (univ.filter (· ∈ P)).filter (· ≠ 1) := by
    intro P hP
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hP
    have hs1 : s ≠ 1 := (Finset.mem_filter.mp hs).2
    ext a
    simp only [Sh, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha1, hDa⟩
      exact ⟨hDa ▸ hmem a ha1, ha1⟩
    · rintro ⟨haP, ha1⟩
      exact ⟨ha1, hconst s hs1 a haP ha1⟩
  have hcardP : ∀ P : Subgroup S, ((univ.filter (· ∈ P)).filter (· ≠ 1)).card + 1 =
      Nat.card P := by
    intro P
    have h := Finset.card_filter_add_card_filter_not (s := univ.filter (· ∈ P)) (fun x : S => x ≠ 1)
    have h1 : ((univ.filter (· ∈ P)).filter (fun x : S => ¬ x ≠ 1)).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨1, by ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
        Finset.mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨h ▸ P.one_mem, h⟩⟩⟩
    rw [h1] at h
    rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hPscard : Ps.card = 10 := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Sh) (t := Ps) (f := D)
      (fun a ha => Finset.mem_image_of_mem D ha)
    have h8 : ∀ P ∈ Ps, (Sh.filter (fun a => D a = P)).card = 8 := by
      intro P hP
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hP
      rw [hfib _ hP]
      have := hcardP (D s)
      rw [hcard s (Finset.mem_filter.mp hs).2] at this
      omega
    rw [Finset.sum_congr rfl h8, Finset.sum_const, smul_eq_mul, hSh80] at h
    omega
  by_contra hno
  push Not at hno
  set Fh : Finset S := Sh.filter (· ∈ F) with hFh
  have hFhcard : Fh.card = 26 := by
    have h := hcardP F
    rw [hF] at h
    have : Fh = (univ.filter (· ∈ F)).filter (· ≠ 1) := by
      ext a; simp [Fh, Sh, and_comm]
    rw [this]
    omega
  have h := Finset.card_eq_sum_card_fiberwise (s := Fh) (t := Ps) (f := D)
    (fun a ha => Finset.mem_image_of_mem D (Finset.mem_filter.mp ha).1)
  have hle : ∀ P ∈ Ps, (Fh.filter (fun a => D a = P)).card ≤ 2 := by
    intro P hP
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hP
    have hs1 : s ≠ 1 := (Finset.mem_filter.mp hs).2
    have heq : Fh.filter (fun a => D a = D s) =
        (univ.filter (· ∈ D s ⊓ F)).filter (· ≠ 1) := by
      ext a
      have := congrArg (a ∈ ·) (hfib _ hP)
      simp only [Fh, Sh, Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf] at this ⊢
      constructor
      · rintro ⟨⟨ha1, haF⟩, hDa⟩
        exact ⟨⟨(this.mp ⟨ha1, hDa⟩).1, haF⟩, ha1⟩
      · rintro ⟨⟨haP, haF⟩, ha1⟩
        exact ⟨⟨ha1, haF⟩, (this.mpr ⟨haP, ha1⟩).2⟩
    rw [heq]
    have h1 := hcardP (D s ⊓ F)
    have hdvd : Nat.card (D s ⊓ F : Subgroup S) ∣ 9 :=
      hcard s hs1 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card (D s ⊓ F : Subgroup S) ≠ 9 := by
      intro h9
      apply hno s hs1
      have heq : D s ⊓ F = D s := Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [h9, hcard s hs1])
      rw [← heq]
      exact inf_le_right
    have : Nat.card (D s ⊓ F : Subgroup S) ≤ 3 := by
      have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [h9] at hdvd
      obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases m <;> simp_all
    omega
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_const, smul_eq_mul, hPscard] at hsum
  omega


end Spread

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)

variable {C : Type*} [Group C] [Finite C]

theorem exists_mul_mem_centralizer_of_alt6 {E : Subgroup C} [E.Normal]
    (eE : E ≃* alternatingGroup (Fin 6)) (hidx : E.index = 9) (c : C) :
    ∃ x ∈ E, c * x⁻¹ ∈ Subgroup.centralizer (E : Set C) := by
  let ρ : C →* MulAut E := MulAut.conjNormal
  set ψ : Outer E := QuotientGroup.mk (ρ c)
  have hc9 : c ^ 9 ∈ E := by
    rw [← hidx]
    have h := pow_card_eq_one' (x := (QuotientGroup.mk c : C ⧸ E))
    rw [← Subgroup.index_eq_card, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    exact h
  have hinnE : ∀ y : C, ∀ hy : y ∈ E, ρ y = MulAut.conj (⟨y, hy⟩ : E) := fun y hy => by
    ext z
    simp [ρ, MulAut.conjNormal_apply]
  have hψ9 : ψ ^ 9 = 1 := by
    rw [← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq_one_iff, hinnE _ hc9]
    exact ⟨_, rfl⟩
  have hout : ¬ 3 ∣ Nat.card (Outer E) := by
    rw [Nat.card_congr (equivalence eE).toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.Item434Alt.not_three_dvd_card_outer_six
  have hψ1 : ψ = 1 := by
    have h1 : orderOf ψ ∣ 9 := orderOf_dvd_of_pow_eq_one hψ9
    have h2 : orderOf ψ ∣ Nat.card (Outer E) := orderOf_dvd_natCard ψ
    have h3 : orderOf ψ = 1 := by
      have : orderOf ψ ∣ 3 ^ 2 := h1
      obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
      rcases m with _ | m
      · simpa using hm'
      · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero m)).trans (hm' ▸ h2)) hout
    exact orderOf_eq_one_iff.mp h3
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (ρ c)).mp hψ1
  refine ⟨x, x.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : (x : C)⁻¹ * y * x ∈ E := E.mul_mem (E.mul_mem (E.inv_mem x.2) hy) x.2
  have h := congrArg (fun φ : MulAut E => ((φ ⟨_, hy'⟩ : E) : C)) hx
  simp only [ρ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h
  have h' : y = c * ((x : C)⁻¹ * y * x) * c⁻¹ := by rw [← h]; group
  calc y * (c * (x : C)⁻¹) = c * ((x : C)⁻¹ * y * x) * c⁻¹ * (c * (x : C)⁻¹) := by
        rw [← h']
    _ = c * (x : C)⁻¹ * y := by group

theorem alt6_split {E : Subgroup C} [E.Normal] (eE : E ≃* alternatingGroup (Fin 6))
    (hidx : E.index = 9) :
    Nat.card (Subgroup.center C) = 9 ∧ Subgroup.center C ⊓ E = ⊥ ∧
      ∀ c : C, ∃ z ∈ Subgroup.center C, ∃ x ∈ E, c = z * x := by
  set K := Subgroup.centralizer (E : Set C) with hK
  have hKE : K ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxE⟩
    have hc : eE ⟨x, hxE⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eE.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxK) y y.2)
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
      map_eq_one_iff _ eE.injective] at hc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hc
  have hKcard : Nat.card K = 9 := by
    rw [← hidx, Subgroup.index_eq_card]
    refine Nat.card_congr (Equiv.ofBijective ((QuotientGroup.mk' E).comp K.subtype) ⟨?_, ?_⟩)
    · intro a b hab
      have h : (a : C)⁻¹ * b ∈ E := by
        rw [← QuotientGroup.ker_mk' E, MonoidHom.mem_ker, map_mul, map_inv]
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hab
        rw [hab, inv_mul_cancel]
      have h2 : (a : C)⁻¹ * b ∈ K ⊓ E := ⟨K.mul_mem (K.inv_mem a.2) b.2, h⟩
      rw [hKE, Subgroup.mem_bot, inv_mul_eq_one] at h2
      exact Subtype.ext h2
    · intro q
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective E q
      obtain ⟨x, hx, hcx⟩ := exists_mul_mem_centralizer_of_alt6 eE hidx c
      refine ⟨⟨c * x⁻¹, hcx⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
      have h1 : QuotientGroup.mk' E x = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx
      rw [h1, inv_one, mul_one]
  have hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcomm := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := K) (by rw [hKcard]; norm_num)
    exact fun a ha b hb => congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hZK : Subgroup.center C = K := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact ((Subgroup.mem_center_iff.mp hz) y)
    · intro k hk
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨x, hx, hcx⟩ := exists_mul_mem_centralizer_of_alt6 eE hidx c
      have h1 : k * (c * x⁻¹) = (c * x⁻¹) * k := hKab _ hk _ hcx
      have h2 : x * k = k * x := (Subgroup.mem_centralizer_iff.mp hk) x hx
      calc c * k = (c * x⁻¹) * (x * k) := by group
        _ = (c * x⁻¹) * (k * x) := by rw [h2]
        _ = k * (c * x⁻¹) * x := by rw [← mul_assoc, ← h1]
        _ = k * c := by group
  refine ⟨hZK ▸ hKcard, hZK ▸ hKE, fun c => ?_⟩
  obtain ⟨x, hx, hcx⟩ := exists_mul_mem_centralizer_of_alt6 eE hidx c
  exact ⟨c * x⁻¹, hZK ▸ hcx, x, hx, by group⟩

theorem exists_alt6_of_mulEquiv {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] {A : Subgroup Y₁}
    {B : Subgroup Y₂} (ψ : A ≃* B) {E : Subgroup A} (hn : E.Normal)
    (eE : E ≃* alternatingGroup (Fin 6)) (hidx : E.index = 9) :
    ∃ E₂ : Subgroup B, E₂.Normal ∧ Nonempty (E₂ ≃* alternatingGroup (Fin 6)) ∧ E₂.index = 9 :=
  ⟨E.map (ψ : A →* B), hn.map _ ψ.surjective,
    ⟨(Subgroup.equivMapOfInjective E (ψ : A →* B) ψ.injective).symm.trans eE⟩,
    (Subgroup.index_map_equiv E ψ).trans hidx⟩

@[expose] noncomputable def centralizerEquiv {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] (φ : Y₁ ≃* Y₂) (a : Y₁) :
    Subgroup.centralizer ({a} : Set Y₁) ≃* Subgroup.centralizer ({φ a} : Set Y₂) :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (CFSG.Sporadic.ONOddCore.centralizer_map_equiv φ a))

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary in
theorem alt6_normal_centralizer_ON
    {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan) {d : Y} (hd : orderOf d = 3) :
    ∃ E : Subgroup (Subgroup.centralizer ({d} : Set Y)), E.Normal ∧
      Nonempty (E ≃* alternatingGroup (Fin 6)) ∧ E.index = 9 := by
  obtain ⟨φ, hφ, hker, hconj, hcard⟩ := on_cover_data
  obtain ⟨E₁, hn, ⟨eE⟩, hq⟩ := alt6_normal_of_cover φ hφ hker hcard
  obtain ⟨g, hg⟩ := hconj (e d) (by rw [MulEquiv.orderOf_eq]; exact hd)
  obtain ⟨θ, hθ⟩ : ∃ θ : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan,
      θ d = φ (CFSG.RankThree.Native.ONTriple.xG 0) := ⟨e.trans (MulAut.conj g⁻¹), by
    show g⁻¹ * e d * g⁻¹⁻¹ = _
    rw [hg]
    group⟩
  generalize φ (CFSG.RankThree.Native.ONTriple.xG 0) = x at E₁ hn eE hq hθ
  subst hθ
  have ψ := (centralizerEquiv θ d).symm
  have hi : E₁.index = 9 := (Subgroup.index_eq_card E₁).trans hq
  exact exists_alt6_of_mulEquiv ψ hn eE hi

section Planes


variable {Y : Type} [Group Y] [Finite Y] (e : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan)

@[expose] noncomputable def centerIn (K : Subgroup Y) : Subgroup Y := (Subgroup.center K).map K.subtype

@[expose] noncomputable def plane (d : Y) : Subgroup Y := centerIn (Subgroup.centralizer ({d} : Set Y))

include e in
theorem plane_facts {d : Y} (hd : orderOf d = 3) :
    Nat.card (Subgroup.centralizer ({d} : Set Y)) = 3240 ∧ Nat.card (plane d) = 9 ∧ d ∈ plane d := by
  obtain ⟨E, hn, ⟨eE⟩, hidx⟩ := alt6_normal_centralizer_ON e hd
  obtain ⟨hZ, -, -⟩ := alt6_split eE hidx
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.card_mul_index E, hidx, Nat.card_congr eE.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  · rw [plane, centerIn, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZ]
  · refine ⟨⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

omit [Finite Y] in
theorem commute_of_mem_centerIn {K : Subgroup Y} {z g : Y} (hz : z ∈ centerIn K) (hg : g ∈ K) :
    g * z = z * g := by
  obtain ⟨z', hz', rfl⟩ := hz
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz') ⟨g, hg⟩)

include e in
theorem pow_three_of_mem_plane {d z : Y} (hd : orderOf d = 3) (hz : z ∈ plane d) : z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eON : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e
  have hp : IsPGroup 3 (plane d) := IsPGroup.of_card (n := 2) (by
    rw [(plane_facts e hd).2.1]; norm_num)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  exact (sylow_three_ON eON P).1.2 z (hP hz)

include e in
theorem centralizer_eq_of_mem_plane {d d' : Y} (hd : orderOf d = 3) (hd' : d' ∈ plane d)
    (hd'1 : d' ≠ 1) :
    Subgroup.centralizer ({d'} : Set Y) = Subgroup.centralizer ({d} : Set Y) := by
  have h3 : orderOf d' = 3 := orderOf_eq_prime (pow_three_of_mem_plane e hd hd') hd'1
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_centerIn hd' hg
  · rw [(plane_facts e h3).1, (plane_facts e hd).1]

include e in
theorem plane_eq_of_mem_plane {d d' : Y} (hd : orderOf d = 3) (hd' : d' ∈ plane d)
    (hd'1 : d' ≠ 1) : plane d' = plane d := by
  rw [plane, plane, centralizer_eq_of_mem_plane e hd hd' hd'1]

include e in
theorem centralizer_plane {d : Y} (hd : orderOf d = 3) :
    Subgroup.centralizer ((plane d : Subgroup Y) : Set Y) = Subgroup.centralizer ({d} : Set Y) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (plane_facts e hd).2.2)
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (commute_of_mem_centerIn hz hg).symm

include e in
theorem plane_le_sylow {d : Y} (hd : orderOf d = 3) (S : Sylow 3 Y) (hdS : d ∈ (S : Subgroup Y)) :
    plane d ≤ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eON : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e
  have hSab := (sylow_three_ON eON S).1
  have hSC : (S : Subgroup Y) ≤ Subgroup.centralizer ({d} : Set Y) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hSab.1.is_comm.comm ⟨s, hs⟩ ⟨d, hdS⟩))
  have hp : IsPGroup 3 (plane d) := IsPGroup.of_card (n := 2) (by
    rw [(plane_facts e hd).2.1]; norm_num)
  have hN : plane d ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have h := commute_of_mem_centerIn hz (hSC hs)
      rw [show z * s * z⁻¹ = s by rw [← h]; group]
      exact hs
    · intro hs
      have h := commute_of_mem_centerIn hz (hSC hs)
      have : s = z⁻¹ * (z * s * z⁻¹) * z := by group
      rw [this, show z⁻¹ * (z * s * z⁻¹) * z = z * s * z⁻¹ by
        rw [← mul_assoc, ← mul_assoc, show z⁻¹ * z * s * z⁻¹ * z = z⁻¹ * (z * s * z⁻¹) * z by
          group]
        calc z⁻¹ * (z * s * z⁻¹) * z = z⁻¹ * (z * s * z⁻¹ * z) := by group
          _ = z⁻¹ * (z * (z * s * z⁻¹)) := by rw [h]
          _ = z * s * z⁻¹ := by group]
      exact hs
  have hsup : IsPGroup 3 ↥(plane d ⊔ (S : Subgroup Y)) := hp.to_sup_of_normal_right' S.isPGroup' hN
  rw [← S.is_maximal' hsup le_sup_right]
  exact le_sup_left

include e in
theorem exists_plane_le_of_card {F : Subgroup Y} (hF : IsPGroup 3 F) (hFc : Nat.card F = 27) :
    ∃ d : Y, orderOf d = 3 ∧ plane d ≤ F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eON : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e
  obtain ⟨S, hFS⟩ := hF.exists_le_sylow
  obtain ⟨hSab, hScard⟩ := sylow_three_ON eON S
  have ho : ∀ s : (S : Subgroup Y), s ≠ 1 → orderOf (s : Y) = 3 := fun s hs =>
    orderOf_eq_prime (hSab.2 _ s.2) (fun h => hs (Subtype.ext h))
  obtain ⟨s, hs1, hsF⟩ := exists_plane_le (S := (S : Subgroup Y))
    (by rw [hScard]; norm_num) (fun s => (plane (s : Y)).subgroupOf S)
    (fun s hs => Subgroup.mem_subgroupOf.mpr (plane_facts e (ho s hs)).2.2)
    (fun s hs => by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (plane_le_sylow e (ho s hs) S s.2)).toEquiv]
      exact (plane_facts e (ho s hs)).2.1)
    (fun s hs t ht ht1 => by
      rw [plane_eq_of_mem_plane e (ho s hs) (Subgroup.mem_subgroupOf.mp ht)
        (fun h => ht1 (Subtype.ext h))])
    (F := F.subgroupOf S) (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFS).toEquiv, hFc])
  refine ⟨s, ho s hs1, fun z hz => ?_⟩
  have hzS : z ∈ (S : Subgroup Y) := plane_le_sylow e (ho s hs1) S s.2 hz
  exact Subgroup.mem_subgroupOf.mp (hsF (Subgroup.mem_subgroupOf.mpr (show ((⟨z, hzS⟩ : S) : Y) ∈ _ from hz)))

end Planes

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
