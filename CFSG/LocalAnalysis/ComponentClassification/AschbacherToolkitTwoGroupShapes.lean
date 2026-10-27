module

public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open

@[expose] def HasDihedralGenerators (P : Type*) [Group P] : Prop :=
  ∃ x y : P, Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ ∧ y ^ 2 = 1 ∧
    y * x * y⁻¹ = x⁻¹ ∧ y ∉ Subgroup.zpowers x

@[expose] def AtMostOneInvolution (P : Type*) [Group P] : Prop :=
  ∀ s t : P, orderOf s = 2 → orderOf t = 2 → s = t

section Transport

variable {P Q : Type*} [Group P] [Group Q]

theorem HasDihedralGenerators.of_mulEquiv (e : P ≃* Q) (h : HasDihedralGenerators P) :
    HasDihedralGenerators Q := by
  obtain ⟨x, y, hgen, hy2, hyx, hy⟩ := h
  refine ⟨e x, e y, ?_, by rw [← map_pow, hy2, map_one], ?_, ?_⟩
  · have hmap := congrArg (Subgroup.map e.toMonoidHom) hgen
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    rw [show (e.toMonoidHom x) = e x from rfl, show (e.toMonoidHom y) = e y from rfl] at hmap
    rw [hmap]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · rw [← map_inv, ← map_mul, ← map_mul, hyx, map_inv]
  · intro hmem
    apply hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective ?_⟩
    rw [map_zpow, hk]

theorem AtMostOneInvolution.of_mulEquiv (e : P ≃* Q) (h : AtMostOneInvolution P) :
    AtMostOneInvolution Q := by
  intro s t hs ht
  have hs' : orderOf (e.symm s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  have ht' : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  exact e.symm.injective (h _ _ hs' ht')

theorem atMostOneInvolution_of_isCyclic [IsCyclic P] : AtMostOneInvolution P := by
  intro s t hs ht
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; omega
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  exact CFSG.RankTwoShapes.eq_of_sq_eq_one_of_isCyclic
    (by rw [← hs]; exact pow_orderOf_eq_one s) hs1
    (by rw [← ht]; exact pow_orderOf_eq_one t) ht1

end Transport

section Suzuki

variable {P : Type*} [Group P] [Finite P]

theorem commute_of_sq_eq_one {G : Type*} [Group G] (h : ∀ g : G, g ^ 2 = 1) (a b : G) :
    a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h (a * b))
  rw [mul_inv_rev, ha, hb] at hab
  exact hab.symm

theorem suzuki_two_group (hP : IsPGroup 2 P) {t : P}
    (hcard : Nat.card (Subgroup.centralizer ({t} : Set P)) = 4)
    (hexp : ∀ x ∈ Subgroup.centralizer ({t} : Set P), x ^ 2 = 1) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) := by
  set V := Subgroup.centralizer ({t} : Set P) with hV
  have htV : t ∈ V := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hVab : IsMulCommutative V := ⟨⟨fun a b =>
    commute_of_sq_eq_one (G := V) (fun g => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp g g.2)) a b⟩⟩
  have hcent : Subgroup.centralizer (V : Set P) = V := by
    apply le_antisymm
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx t htV).symm
    · intro v hv
      apply Subgroup.mem_centralizer_iff.mpr
      intro w hw
      exact congrArg Subtype.val (hVab.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hv⟩)
  exact CFSG.RankTwoShapes.selfCentralizing_four_shapes hP V hVab hexp hcard hcent

end Suzuki

section Generators

variable {R : Type*} [Group R]

theorem exists_inverting_generators_of_dihedral [Finite R] {m : ℕ} [NeZero m]
    (e : R ≃* DihedralGroup m) :
    ∃ ρ σ : R, (Subgroup.zpowers ρ).index = 2 ∧ σ ∉ Subgroup.zpowers ρ ∧
      σ * ρ ^ 2 * σ⁻¹ = (ρ ^ 2)⁻¹ := by
  refine ⟨e.symm (DihedralGroup.r 1), e.symm (DihedralGroup.sr 0), ?_, ?_, ?_⟩
  · have h1 := (Subgroup.zpowers (e.symm (DihedralGroup.r 1))).card_mul_index
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h1
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact Nat.eq_of_mul_eq_mul_left hm (h1.trans (mul_comm 2 m))
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 := congrArg e hk
    rw [map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · rw [zpow_natCast, DihedralGroup.r_one_pow] at h2
      cases h2
    · rw [zpow_neg, zpow_natCast, DihedralGroup.r_one_pow, DihedralGroup.inv_r] at h2
      cases h2
  · apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, sq,
      DihedralGroup.r_mul_r, DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.inv_r,
      DihedralGroup.sr_mul_sr]
    congr 1
    ring

theorem exists_inverting_generators_of_semidihedral [Finite R] {n : ℕ} (hn : 4 ≤ n)
    (e : R ≃* SemidihedralGroup n) :
    ∃ ρ σ : R, (Subgroup.zpowers ρ).index = 2 ∧ σ ∉ Subgroup.zpowers ρ ∧
      σ * ρ ^ 2 * σ⁻¹ = (ρ ^ 2)⁻¹ := by
  set r := CFSG.Semidihedral.r n
  set s := CFSG.Semidihedral.s n
  have hidx : (Subgroup.zpowers r).index = 2 := CFSG.Semidihedral.rotation_index n (by omega)
  have hsr : s ∉ Subgroup.zpowers r := by
    intro hmem
    have hle : Subgroup.closure (Set.range (PresentedGroup.of (rels := semidihedralRels n)))
        ≤ Subgroup.zpowers r := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.mem_zpowers r
      · exact hmem
    rw [PresentedGroup.closure_range_of, top_le_iff] at hle
    rw [hle, Subgroup.index_top] at hidx
    omega
  have hord : orderOf r = 2 ^ (n - 1) := CFSG.Semidihedral.orderOf_r n (by omega)
  have hconj : s * r * s⁻¹ = r ^ (2 ^ (n - 2) - 1) := CFSG.Semidihedral.s_conj_r n
  have hinv : s * r ^ 2 * s⁻¹ = (r ^ 2)⁻¹ := by
    have h1 : s * r ^ 2 * s⁻¹ = (s * r * s⁻¹) ^ 2 := by rw [conj_pow]
    rw [h1, hconj, ← pow_mul, eq_inv_iff_mul_eq_one, ← pow_add,
      ← orderOf_dvd_iff_pow_eq_one, hord]
    have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
    refine ⟨1, ?_⟩
    rw [h2]
    omega
  refine ⟨e.symm r, e.symm s, ?_, ?_, ?_⟩
  · have hmap : Subgroup.zpowers (e.symm r) = (Subgroup.zpowers r).map e.symm.toMonoidHom :=
      (MonoidHom.map_zpowers e.symm.toMonoidHom r).symm
    rw [hmap, Subgroup.index_map_of_bijective e.symm.bijective]
    exact hidx
  · intro hmem
    apply hsr
    have := Subgroup.mem_map_of_mem e.toMonoidHom hmem
    rwa [MonoidHom.map_zpowers, show e.toMonoidHom (e.symm r) = r from e.apply_symm_apply r,
      show e.toMonoidHom (e.symm s) = s from e.apply_symm_apply s] at this
  · apply e.injective
    simp only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]
    exact hinv

end Generators

section IndexTwo

variable {R : Type*} [Group R] [Finite R]

theorem index_two_subgroup_shape (ρ σ : R) (hidx : (Subgroup.zpowers ρ).index = 2)
    (hσ : σ ∉ Subgroup.zpowers ρ) (hinv : σ * ρ ^ 2 * σ⁻¹ = (ρ ^ 2)⁻¹)
    (Q : Subgroup R) (hQ : Q.index = 2) :
    AtMostOneInvolution Q ∨ HasDihedralGenerators Q := by
  set C := Subgroup.zpowers ρ with hC
  have hcardR : Nat.card R = 2 * Nat.card C := by
    rw [← C.card_mul_index, hidx, mul_comm]
  have hcardQ : Nat.card Q = Nat.card C := by
    have h := Q.card_mul_index
    rw [hQ, hcardR] at h
    omega
  have hout : ∀ y : R, y ∉ C → y * ρ ^ 2 * y⁻¹ = (ρ ^ 2)⁻¹ := by
    intro y hy
    have hσy : σ⁻¹ * y ∈ C := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (fun h => hσ (by simpa using C.inv_mem h)) hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσy
    have hy' : y = σ * ρ ^ k := by rw [hk]; group
    rw [hy', ← hinv]
    group
  by_cases hρQ : ρ ∈ Q
  ·
    left
    have hCQ : C ≤ Q := Subgroup.zpowers_le.mpr hρQ
    have hCQ' : C = Q := Subgroup.eq_of_le_of_card_ge hCQ hcardQ.le
    have : IsCyclic Q := by
      rw [← hCQ']
      exact Subgroup.isCyclic_zpowers ρ
    exact atMostOneInvolution_of_isCyclic
  have hρ2Q : ρ ^ 2 ∈ Q := by
    rw [sq, Subgroup.mul_mem_iff_of_index_two hQ]
  obtain ⟨y, hyQ, hyC⟩ : ∃ y ∈ Q, y ∉ C := by
    by_contra hnone
    push Not at hnone
    have hQC : Q ≤ C := fun q hq => hnone q hq
    have := Subgroup.eq_of_le_of_card_ge hQC hcardQ.ge
    exact hρQ (this ▸ Subgroup.mem_zpowers ρ)
  set x : Q := ⟨ρ ^ 2, hρ2Q⟩ with hx
  set y' : Q := ⟨y, hyQ⟩ with hy'
  have hyx : y' * x * y'⁻¹ = x⁻¹ := Subtype.ext (hout y hyC)
  have hy'x : y' ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hyC
    have hyk : y = (ρ ^ 2) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [hyk]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers ρ) 2) k
  have hρodd : orderOf ρ % 2 = 0 := by
    by_contra hodd
    apply hρQ
    have hcop : Nat.Coprime 2 (orderOf ρ) := by
      rw [Nat.coprime_two_left]
      exact Nat.odd_iff.mpr (by omega)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hρ2Q m
  have hxcard : 2 * Nat.card (Subgroup.zpowers x) = Nat.card Q := by
    rw [hcardQ, Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk,
      orderOf_pow' ρ two_ne_zero, Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hρodd)]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hρodd)
  have hxidx : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [← hxcard] at h
    have hpos : 0 < Nat.card (Subgroup.zpowers x) := Nat.card_pos
    nlinarith
  have hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y' = ⊤ :=
    (CFSG.RankTwoShapes.top_eq_sup_zpowers_of_index_two hxidx hy'x).symm
  by_cases hy2 : y' ^ 2 = 1
  · right
    exact ⟨x, y', hgen, hy2, hyx, hy'x⟩
  · left
    have hy2C : y ^ 2 ∈ C := by
      rw [sq, Subgroup.mul_mem_iff_of_index_two hidx]
    have hy2x : Commute (y' ^ 2) x := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy2C
      apply Subtype.ext
      change y ^ 2 * ρ ^ 2 = ρ ^ 2 * y ^ 2
      rw [← hk]
      exact ((Commute.refl ρ).zpow_left k).pow_right 2 |>.eq
    have hsq : ∀ q : Q, q ∉ Subgroup.zpowers x → q ^ 2 ≠ 1 := by
      intro q hq hq2
      have hyq : y'⁻¹ * q ∈ Subgroup.zpowers x := by
        rw [Subgroup.mul_mem_iff_of_index_two hxidx]
        exact iff_of_false (fun h => hy'x (by simpa using (Subgroup.zpowers x).inv_mem h)) hq
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyq
      have hq' : q = y' * x ^ k := by rw [hk]; group
      have hconjk : y' * x ^ k * y'⁻¹ = (x ^ k)⁻¹ := by
        rw [← conj_zpow, hyx, inv_zpow]
      have hcomm : (x ^ k)⁻¹ * y' ^ 2 = y' ^ 2 * (x ^ k)⁻¹ :=
        ((hy2x.zpow_right k).inv_right).eq.symm
      apply hy2
      rw [← hq2, hq']
      calc y' ^ 2 = (x ^ k)⁻¹ * y' ^ 2 * x ^ k := by rw [hcomm]; group
        _ = (y' * x ^ k * y'⁻¹) * y' ^ 2 * x ^ k := by rw [hconjk]
        _ = (y' * x ^ k) ^ 2 := by simp only [sq]; group
    intro s t hs ht
    have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have hsx : s ∈ Subgroup.zpowers x := by
      by_contra h
      exact hsq s h hs2
    have htx : t ∈ Subgroup.zpowers x := by
      by_contra h
      exact hsq t h ht2
    have h := atMostOneInvolution_of_isCyclic (P := Subgroup.zpowers x) ⟨s, hsx⟩ ⟨t, htx⟩
      (by rw [Subgroup.orderOf_mk]; exact hs) (by rw [Subgroup.orderOf_mk]; exact ht)
    exact congrArg Subtype.val h

end IndexTwo

section SmallCentralizer

theorem atMostOneInvolution_of_card_le_two {P : Type*} [Group P] [Finite P]
    (h : Nat.card P ≤ 2) : AtMostOneInvolution P := by
  intro s t hs ht
  have hle : Nat.card P ≤ Nat.card (Subgroup.zpowers s) := by
    rw [Nat.card_zpowers, hs]
    exact h
  have htop : Subgroup.zpowers s = ⊤ := Subgroup.eq_top_of_le_card _ hle
  have htmem : t ∈ Subgroup.zpowers s := htop ▸ Subgroup.mem_top t
  rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hs htmem with h1 | h1
  · rw [h1, orderOf_one] at ht
    omega
  · exact h1.symm

variable {R : Type*} [Group R] [Finite R]

theorem index_two_small_centralizer_shape (hR : IsPGroup 2 R) (P : Subgroup R)
    (hP : P.index = 2) {b : R} (hb : orderOf b = 2) (hbP : b ∉ P)
    (hC : Nat.card (P ⊓ Subgroup.centralizer ({b} : Set R) : Subgroup R) ≤ 2) :
    AtMostOneInvolution P ∨ HasDihedralGenerators P := by
  set Cb := Subgroup.centralizer ({b} : Set R) with hCb
  have hbCb : b ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hP
  have hrel : P.relIndex Cb = 2 := by
    have hdvd : P.relIndex Cb ∣ 2 := hP ▸ Subgroup.relIndex_dvd_index_of_normal P Cb
    have hne : P.relIndex Cb ≠ 1 := by
      intro h1
      exact hbP (Subgroup.relIndex_eq_one.mp h1 hbCb)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hcardCb : Nat.card Cb = 2 * Nat.card (P ⊓ Cb : Subgroup R) := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := Cb)
    rw [hrel] at h
    exact h.symm
  have hpos : 0 < Nat.card (P ⊓ Cb : Subgroup R) := Nat.card_pos
  by_cases h1 : Nat.card (P ⊓ Cb : Subgroup R) = 1
  ·
    left
    apply atMostOneInvolution_of_card_le_two
    have hCb2 : Nat.card Cb = 2 := by rw [hcardCb, h1]
    have hbz : Subgroup.zpowers b = Cb := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbCb)
      rw [hCb2, Nat.card_zpowers, hb]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial R := ⟨⟨b, 1, fun h => by rw [h, orderOf_one] at hb; omega⟩⟩
    have hZ := hR.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center R)
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzCb : z ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp hz b).symm
    rw [← hbz] at hzCb
    rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hb hzCb with h | h
    · exact absurd h hz1'
    · have hbc : b ∈ Subgroup.center R := h ▸ hz
      have htop : Cb = ⊤ := by
        rw [eq_top_iff]
        intro g _
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_center_iff.mp hbc g)
      have hR2 : Nat.card R = 2 := by rw [← Subgroup.card_top, ← htop, hCb2]
      have h2 := P.card_mul_index
      rw [hP, hR2] at h2
      omega
  ·
    have h2 : Nat.card (P ⊓ Cb : Subgroup R) = 2 := by omega
    have hcard4 : Nat.card Cb = 4 := by rw [hcardCb, h2]
    have hexp : ∀ x ∈ Cb, x ^ 2 = 1 := by
      intro x hx
      have hsq : ∀ y ∈ P ⊓ Cb, y ^ 2 = 1 := by
        intro y hy
        have h := orderOf_dvd_natCard (⟨y, hy⟩ : (P ⊓ Cb : Subgroup R))
        rw [h2] at h
        have := (orderOf_dvd_iff_pow_eq_one.mp h)
        exact congrArg Subtype.val this
      by_cases hxP : x ∈ P
      · exact hsq x ⟨hxP, hx⟩
      · have hxb : x * b ∈ P := by
          rw [Subgroup.mul_mem_iff_of_index_two hP]
          exact iff_of_false hxP hbP
        have hxbC : x * b ∈ Cb := Cb.mul_mem hx hbCb
        have hcomm : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx
        have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
        have h := hsq (x * b) ⟨hxb, hxbC⟩
        have hxx : x ^ 2 = (x * b) ^ 2 := by
          calc x ^ 2 = x * x * (b * b) := by rw [← sq b, hb2, mul_one, sq]
            _ = x * (x * b) * b := by group
            _ = x * (b * x) * b := by rw [hcomm]
            _ = (x * b) ^ 2 := by rw [sq]; group
        rw [hxx, h]
    rcases suzuki_two_group hR hcard4 hexp with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
      obtain ⟨ρ, σ, hidx, hσ, hinv⟩ := exists_inverting_generators_of_dihedral e
      exact index_two_subgroup_shape ρ σ hidx hσ hinv P hP
    · obtain ⟨ρ, σ, hidx, hσ, hinv⟩ := exists_inverting_generators_of_semidihedral hn e
      exact index_two_subgroup_shape ρ σ hidx hσ hinv P hP

@[expose] def fixedSubgroup {P : Type*} [Group P] (β : MulAut P) : Subgroup P :=
  β.toMonoidHom.eqLocus (MonoidHom.id P)

theorem mem_fixedSubgroup {P : Type*} [Group P] {β : MulAut P} {p : P} :
    p ∈ fixedSubgroup β ↔ β p = p :=
  Iff.rfl

theorem involutory_automorphism_shape {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (β : MulAut P) (hβ : β ^ 2 = 1)
    (hfix : Nat.card (fixedSubgroup β) ≤ 2) :
    AtMostOneInvolution P ∨ HasDihedralGenerators P := by
  by_cases hβ1 : β = 1
  · left
    apply atMostOneInvolution_of_card_le_two
    have htop : fixedSubgroup β = ⊤ := by
      rw [eq_top_iff]
      intro p _
      rw [mem_fixedSubgroup, hβ1]
      rfl
    rw [htop, Subgroup.card_top] at hfix
    exact hfix
  have hβord : orderOf β = 2 := orderOf_eq_prime hβ hβ1
  set A := Subgroup.zpowers β with hA
  let φ : A →* MulAut P := A.subtype
  have : Finite A := inferInstance
  have hfinR : Finite (P ⋊[φ] A) :=
    Finite.of_injective (fun t : P ⋊[φ] A => (t.left, t.right)) fun t u h =>
      SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hcardA : Nat.card A = 2 := by rw [hA, Nat.card_zpowers, hβord]
  have hcardR : Nat.card (P ⋊[φ] A) = Nat.card P * 2 := by
    rw [SemidirectProduct.card, hcardA]
  have hR : IsPGroup 2 (P ⋊[φ] A) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    exact IsPGroup.of_card (n := k + 1) (by rw [hcardR, hk, pow_succ])
  let P' : Subgroup (P ⋊[φ] A) := (SemidirectProduct.inl : P →* P ⋊[φ] A).range
  let e : P ≃* P' := MonoidHom.ofInjective SemidirectProduct.inl_injective
  have hcardP' : Nat.card P' = Nat.card P := (Nat.card_congr e.toEquiv).symm
  have hP' : P'.index = 2 := by
    have h := P'.card_mul_index
    rw [hcardP', hcardR] at h
    have hpos : 0 < Nat.card P := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h
  let b : P ⋊[φ] A := SemidirectProduct.inr ⟨β, Subgroup.mem_zpowers β⟩
  have hb : orderOf b = 2 := by
    rw [orderOf_injective _ SemidirectProduct.inr_injective, Subgroup.orderOf_mk, hβord]
  have hbP' : b ∉ P' := by
    rintro ⟨p, hp⟩
    have h := congrArg SemidirectProduct.rightHom hp
    rw [SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr] at h
    exact hβ1 (congrArg Subtype.val h).symm
  have hcent : P' ⊓ Subgroup.centralizer ({b} : Set (P ⋊[φ] A)) =
      (fixedSubgroup β).map SemidirectProduct.inl := by
    ext t
    constructor
    · rintro ⟨⟨p, rfl⟩, ht⟩
      refine ⟨p, ?_, rfl⟩
      change β p = p
      have hc : SemidirectProduct.inl p * b = b * SemidirectProduct.inl p :=
        Subgroup.mem_centralizer_singleton_iff.mp ht
      have haut : (SemidirectProduct.inl (β p) : P ⋊[φ] A) =
          b * SemidirectProduct.inl p * b⁻¹ := by
        have h := SemidirectProduct.inl_aut (φ := φ) ⟨β, Subgroup.mem_zpowers β⟩ p
        rw [map_inv] at h
        exact h
      have h1 : (SemidirectProduct.inl (β p) : P ⋊[φ] A) = SemidirectProduct.inl p := by
        rw [haut, ← hc]
        group
      exact SemidirectProduct.inl_injective h1
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, rfl⟩, ?_⟩
      change β p = p at hp
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have haut : (SemidirectProduct.inl (β p) : P ⋊[φ] A) =
          b * SemidirectProduct.inl p * b⁻¹ := by
        have h := SemidirectProduct.inl_aut (φ := φ) ⟨β, Subgroup.mem_zpowers β⟩ p
        rw [map_inv] at h
        exact h
      rw [hp] at haut
      calc SemidirectProduct.inl p * b
          = (b * SemidirectProduct.inl p * b⁻¹) * b := by rw [← haut]
        _ = b * SemidirectProduct.inl p := by group
  have hC : Nat.card (P' ⊓ Subgroup.centralizer ({b} : Set (P ⋊[φ] A)) :
      Subgroup (P ⋊[φ] A)) ≤ 2 := by
    rw [hcent, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
    exact hfix
  rcases index_two_small_centralizer_shape hR P' hP' hb hbP' hC with h | h
  · exact Or.inl (h.of_mulEquiv e.symm)
  · exact Or.inr (h.of_mulEquiv e.symm)

end SmallCentralizer

end CFSG.ComponentClassification.AschbacherToolkit
