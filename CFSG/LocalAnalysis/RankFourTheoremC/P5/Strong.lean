module

import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.BorelDataP
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Ctx

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_mul_mem_normalizer_zpowers_p {p : ℕ} [Fact p.Prime] {P : Sylow p G} {x : G}
    {C : Subgroup G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hxp : x ^ p = 1) (hxC : x ∈ C) {m : G} (hx'C : m * x * m⁻¹ ∈ C) :
    ∃ c ∈ C, c * m ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  have hprime : Nat.Prime p := Fact.out
  have hp3 : ∀ y : G, y ∈ C → y ^ p = 1 → ∃ S : Subgroup G, IsSylowOf p S C ∧ y ∈ S := by
    intro y hy hy3
    have hyp : IsPGroup p ((zpowers y).subgroupOf C) := by
      have : IsPGroup p (zpowers y) := by
        have hyo : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy3
        rcases (Nat.dvd_prime hprime).mp hyo with h | h
        · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
        · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
      exact this.comap_subtype
    obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
    exact ⟨(Q : Subgroup C).map C.subtype, ⟨Q, rfl⟩,
      ⟨⟨y, hy⟩, hQ (Subgroup.mem_subgroupOf.mpr (mem_zpowers y)), rfl⟩⟩
  obtain ⟨S₁, hS₁, hxS₁⟩ := hp3 x hxC hxp
  have hx'p : (m * x * m⁻¹) ^ p = 1 := by rw [conj_pow, hxp]; simp
  obtain ⟨S₂, hS₂, hx'S₂⟩ := hp3 _ hx'C hx'p
  obtain ⟨k, hkC, hk⟩ := hS₁.exists_mem_conj hS₂
  have hyS₁ : k⁻¹ * (m * x * m⁻¹) * k ∈ S₁ := (hk _).mp hx'S₂
  obtain ⟨P', hP'⟩ := hS₁.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hS₁P : ∀ y ∈ S₁, g⁻¹ * y * g ∈ (P : Subgroup G) := by
    intro y hy
    have hyP' : y ∈ ((g • P : Sylow p G) : Subgroup G) := by rw [hg]; exact hP' hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hyP'
    exact hyP'
  have hconjP : ∀ y ∈ S₁, (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    intro y hy
    rw [map_conj_zpowers', zpowers_le]
    have := hS₁P y hy
    simpa [mul_assoc] using this
  set c : G := k⁻¹ with hc
  set y : G := k⁻¹ * (m * x * m⁻¹) * k with hy
  have hcC : c ∈ C := C.inv_mem hkC
  have h1 : (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom = zpowers x :=
    hwc g⁻¹ (hconjP x hxS₁)
  have h1' : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h1
    rw [Subgroup.map_map] at this
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply]
      group
    rw [hid, Subgroup.map_id] at this
    exact this.symm
  have hyx : zpowers y = (zpowers x).map (MulAut.conj (c * m)).toMonoidHom := by
    rw [map_conj_zpowers', hy, hc]
    congr 1
    group
  have hcomp : (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom =
      (zpowers x).map (MulAut.conj (g⁻¹ * (c * m))).toMonoidHom := by
    rw [hyx, Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply]
  have h2 : (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom = zpowers x := by
    rw [hcomp]
    exact hwc _ (hcomp ▸ hconjP y hyS₁)
  have h3 : zpowers y = zpowers x := by
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h2
    rw [Subgroup.map_map] at this
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply]
      group
    rw [hid, Subgroup.map_id, h1'] at this
    exact this
  refine ⟨c, hcC, mem_normalizer_of_map_conj_le ?_⟩
  rw [← hyx, h3]

theorem exists_centralizer_mul_mem_normalizer_zpowers_p {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {x : G} {E : Subgroup G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hxp : x ^ p = 1) (hxE : ∀ e ∈ E, x * e = e * x) {m : G} (hmE : m ∈ normalizer (E : Set G)) :
    ∃ c ∈ centralizer (E : Set G), c * m ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  set C : Subgroup G := centralizer (E : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_iff.mpr fun e he => (hxE e he).symm
  have hx'C : m * x * m⁻¹ ∈ C := by
    rw [mem_centralizer_iff]
    intro e he
    have h1 : m⁻¹ * e * m ∈ E := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hmE) e).mp he
      simpa using this
    have h2 := hxE _ h1
    calc e * (m * x * m⁻¹) = m * ((m⁻¹ * e * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * e * m)) * m⁻¹ := by rw [h2]
      _ = m * x * m⁻¹ * e := by group
  exact exists_mem_mul_mem_normalizer_zpowers_p hwc hxp hxC hx'C

theorem exists_mul_mem_of_mem_sup_p {p : ℕ} [Fact p.Prime] {P : Sylow p G} {O : Subgroup G}
    (hPO : (P : Subgroup G) ≤ normalizer (O : Set G)) {t : G}
    (ht : t ∈ (P : Subgroup G) ⊔ O) (htp : t ^ p = 1) :
    ∃ o ∈ O, o * t * o⁻¹ ∈ (P : Subgroup G) := by
  have hprime : Nat.Prime p := Fact.out
  have hz : IsPGroup p (zpowers t) := by
    have hto : orderOf t ∣ p := orderOf_dvd_of_pow_eq_one htp
    rcases (Nat.dvd_prime hprime).mp hto with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨y, hy⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P
    ((P : Subgroup G) ⊔ O) le_sup_left (zpowers t) hz (zpowers_le.mpr ht)
  have hty : (y : G) * t * (y : G)⁻¹ ∈ (P : Subgroup G) := hy ⟨t, mem_zpowers t, rfl⟩
  have hyset : (y : G) ∈ (↑((P : Subgroup G) ⊔ O) : Set G) := y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (P : Subgroup G) O hPO] at hyset
  obtain ⟨r, hr, o, ho, hro⟩ := hyset
  refine ⟨o, ho, ?_⟩
  have h1 : o * t * o⁻¹ = r⁻¹ * ((y : G) * t * (y : G)⁻¹) * r := by
    rw [← hro]
    group
  rw [h1]
  exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hr) hty) hr

section Action

variable (p : ℕ) (x : G)

omit [Finite G] in
private theorem normalizer_zpowers_le_normalizer_centralizer' :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤
      normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hCeq : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have := normalizer_le_normalizer_centralizer (zpowers x : Subgroup G)
  rwa [hCeq] at this

private noncomputable def actC :
    normalizer ((zpowers x : Subgroup G) : Set G) →* MulAut (centralizer ({x} : Set G)) :=
  (centralizer ({x} : Set G)).normalizerMonoidHom.comp
    (Subgroup.inclusion (normalizer_zpowers_le_normalizer_centralizer' x))

omit [Finite G] in
private theorem actC_coe (n : normalizer ((zpowers x : Subgroup G) : Set G))
    (c : centralizer ({x} : Set G)) :
    ((actC x n c : centralizer ({x} : Set G)) : G) = n * c * n⁻¹ := by
  simp [actC, Subgroup.normalizerMonoidHom_apply_apply_coe]

omit [Finite G] in
private theorem map_actC (n : normalizer ((zpowers x : Subgroup G) : Set G)) :
    (primeComplementCore (G := centralizer ({x} : Set G)) p).map (actC x n).toMonoidHom =
      primeComplementCore (G := centralizer ({x} : Set G)) p := by
  have hchar : (primeComplementCore (G := centralizer ({x} : Set G)) p).Characteristic :=
    primeComplementCore_characteristic p
  exact (Subgroup.map_equiv_eq_comap_symm (actC x n) _).trans (hchar.fixed (actC x n).symm)

private noncomputable def actX (n : normalizer ((zpowers x : Subgroup G) : Set G)) :
    MulAut (RedCent p x) :=
  QuotientGroup.congr (primeComplementCore (G := centralizer ({x} : Set G)) p)
    (primeComplementCore (G := centralizer ({x} : Set G)) p) (actC x n) (map_actC p x n)

omit [Finite G] in
private theorem actX_mk (n : normalizer ((zpowers x : Subgroup G) : Set G))
    (c : centralizer ({x} : Set G)) :
    actX p x n (QuotientGroup.mk c) = QuotientGroup.mk (actC x n c) := rfl

end Action

namespace BorelDataP

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G} {n : ℕ}
  {f : GaloisField p n → G} {W : Subgroup G}

theorem conj_mem_QK_of_mem_normalizer (hB : BorelDataP p P M x f W) {g : G}
    (hg : g ∈ normalizer ((zpowers x : Subgroup G) : Set G)) {q : G} (hq : q ∈ hB.QK)
    (hgq : g * q * g⁻¹ ∈ (P : Subgroup G)) : g * q * g⁻¹ ∈ hB.QK := by
  obtain ⟨R, K, d, hfacts, hd, ⟨eK⟩, hρ, hsurj, -, -, hReq⟩ := hB.reduced
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
  have hKchar : ∀ σ : MulAut (RedCent p x), K.map σ.toMonoidHom = K := fun σ =>
    hfacts.red.unique _
      ((CFSG.ComponentClassification.LocalComponents.equiv_iff σ K).mpr hfacts.red.component)
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Qc : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQc
  have hQcp : IsPGroup p Qc :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  have hinj := injOn_mk_of_isPGroup (primeComplementCore_coprime (G := C) p) hQcp
  have hftC : f t ∈ C := mem_centralizer_singleton_iff.mpr (hB.f_comm t)
  obtain ⟨hc, hρt, -⟩ := hρ t
  set ν : normalizer ((zpowers x : Subgroup G) : Set G) := ⟨g, hg⟩ with hν
  have h1 : actX p x ν (QuotientGroup.mk ⟨f t, hftC⟩) =
      QuotientGroup.mk (actC x ν ⟨f t, hftC⟩) :=
    actX_mk p x ν _
  have hcoe : ((actC x ν ⟨f t, hftC⟩ : C) : G) = g * f t * g⁻¹ := actC_coe x ν _
  have hKmem : QuotientGroup.mk (actC x ν ⟨f t, hftC⟩) ∈ K := by
    rw [← h1]
    have : QuotientGroup.mk (⟨f t, hftC⟩ : C) ∈ K := hρt.2
    have h2 : actX p x ν (QuotientGroup.mk ⟨f t, hftC⟩) ∈ K.map (actX p x ν).toMonoidHom :=
      ⟨_, this, rfl⟩
    rwa [hKchar] at h2
  have hmemQc : (actC x ν ⟨f t, hftC⟩ : C) ∈ Qc := by
    rw [hQc, mem_subgroupOf, hcoe]
    exact ⟨hgq, (actC x ν ⟨f t, hftC⟩).2⟩
  have hRmem : QuotientGroup.mk (actC x ν ⟨f t, hftC⟩) ∈ (R : Subgroup (RedCent p x)) := by
    rw [hReq]
    exact ⟨_, hmemQc, rfl⟩
  obtain ⟨s, hcs, hs⟩ := hsurj _ ⟨hRmem, hKmem⟩
  have hsQ : (⟨f s, hcs⟩ : C) ∈ Qc := by
    rw [hQc, mem_subgroupOf]
    exact ⟨(hB.le (hB.f_mem_W s)).1, hcs⟩
  have heq := hinj _ hsQ _ hmemQc hs
  refine hB.mem_QK.mpr ⟨s, ?_⟩
  rw [← hcoe, ← heq]

theorem conj_mem_QK_of_conj_mem_P (hB : BorelDataP p P M x f W) (hS : PtShape p P x) {g q : G}
    (hq : q ∈ hB.QK) (hgq : g * q * g⁻¹ ∈ (P : Subgroup G)) : g * q * g⁻¹ ∈ hB.QK := by
  haveI : IsMulCommutative (P : Subgroup G) := hS.abelian
  have hcomm : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hqP : q ∈ (P : Subgroup G) := hB.QK_le_P hq
  have hxC : x ∈ centralizer ({q} : Set G) := mem_centralizer_singleton_iff.mpr
    (hcomm x hB.x_mem q hqP)
  have hx'C : g⁻¹ * x * (g⁻¹)⁻¹ ∈ centralizer ({q} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := hcomm x hB.x_mem _ hgq
    calc g⁻¹ * x * (g⁻¹)⁻¹ * q = g⁻¹ * (x * (g * q * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * q * g⁻¹) * x) * g := by rw [h1]
      _ = q * (g⁻¹ * x * (g⁻¹)⁻¹) := by group
  obtain ⟨c, hc, hcg⟩ := exists_mem_mul_mem_normalizer_zpowers_p hS.weak hB.x_pow hxC hx'C
  have hcq : c * q = q * c := mem_centralizer_singleton_iff.mp hc
  have hνN : g * c⁻¹ ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    have := Subgroup.inv_mem _ hcg
    simpa [mul_assoc] using this
  have hν : (g * c⁻¹) * q * (g * c⁻¹)⁻¹ = g * q * g⁻¹ := by
    calc (g * c⁻¹) * q * (g * c⁻¹)⁻¹ = g * (c⁻¹ * q * c) * g⁻¹ := by group
      _ = g * q * g⁻¹ := by
        have h2 : c⁻¹ * q * c = q := by
          calc c⁻¹ * q * c = c⁻¹ * (q * c) := by group
            _ = c⁻¹ * (c * q) := by rw [← hcq]
            _ = q := by group
        rw [h2]
  have := hB.conj_mem_QK_of_mem_normalizer hνN hq (by rw [hν]; exact hgq)
  rwa [hν] at this

theorem le_normalizer_QK_sup (hB : BorelDataP p P M x f W) (hS : PtShape p P x) {O : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hOM : M ≤ normalizer (O : Set G))
    (hcontain : ∀ m ∈ M, ∀ q ∈ hB.QK, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ O) :
    M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G) := by
  intro m hm
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    have hq3 : (m * q * m⁻¹) ^ p = 1 := by rw [conj_pow, hB.QK_pow_p hq]; simp
    obtain ⟨o, ho, hot⟩ := exists_mul_mem_of_mem_sup_p (fun a ha => hOM (hPM ha))
      (hcontain m hm q hq) hq3
    have hg : (o * m) * q * (o * m)⁻¹ = o * (m * q * m⁻¹) * o⁻¹ := by group
    have hq' := hB.conj_mem_QK_of_conj_mem_P hS hq (by rw [hg]; exact hot)
    rw [hg] at hq'
    have h2 : (MulAut.conj m).toMonoidHom q = o⁻¹ * (o * (m * q * m⁻¹) * o⁻¹) * o := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2]
    set q' := o * (m * q * m⁻¹) * o⁻¹ with hq'def
    have hq'M : q' ∈ M := hPM (hB.QK_le_P hq')
    have h3 : o⁻¹ * q' * o = (o⁻¹ * (q' * o * q'⁻¹)) * q' := by group
    rw [h3]
    have hO' : q' * o * q'⁻¹ ∈ O := (mem_normalizer_iff.mp (hOM hq'M) o).mp ho
    exact Subgroup.mul_mem _ (mem_sup_right (O.mul_mem (O.inv_mem ho) hO')) (mem_sup_left hq')
  · rintro _ ⟨o, ho, rfl⟩
    exact mem_sup_right ((mem_normalizer_iff.mp (hOM hm) o).mp ho)

end BorelDataP

end CFSG.LocalAnalysis.RankFourTheoremC.P5
