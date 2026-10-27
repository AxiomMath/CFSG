module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.OddCover
open scoped commutatorElement

section Reduce

variable {G : Type*} [Group G] [Finite G] {r : ℕ} [hr : Fact r.Prime]

theorem pRank_quot_eq_of_le (A B : Subgroup G) [A.Normal] [B.Normal] (hAB : A ≤ B)
    (hA : IsPGroup r A) (h : ∀ y ∈ B, (∃ k : ℕ, y ^ (r ^ k) = 1) → y ∈ A) :
    CFSG.Open.pRank r (⊤ : Subgroup (G ⧸ B)) = CFSG.Open.pRank r (⊤ : Subgroup (G ⧸ A)) := by
  haveI : (B.map (QuotientGroup.mk' A)).Normal := Subgroup.Normal.map ‹B.Normal› _
    (QuotientGroup.mk'_surjective A)
  have e := QuotientGroup.quotientQuotientEquivQuotient A B hAB
  rw [← pRank_top_eq_of_mulEquiv hr.out.one_lt e]
  refine pRank_quotient_eq (B.map (QuotientGroup.mk' A)) ?_
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B.map (QuotientGroup.mk' A))) r hdvd
  obtain ⟨y, hyB, hy⟩ := Subgroup.mem_map.1 x.2
  have hxr : (x : G ⧸ A) ^ r = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hyr : y ^ r ∈ A := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    simpa [← hy] using hxr
  obtain ⟨k, hk⟩ := hA ⟨y ^ r, hyr⟩
  have hyk : y ^ (r ^ (k + 1)) = 1 := by
    have := congrArg Subtype.val hk
    rw [pow_succ', pow_mul]
    exact this
  have hyA : y ∈ A := h y hyB ⟨k + 1, hyk⟩
  have hx1 : (x : G ⧸ A) = 1 := by
    rw [← hy]
    exact (QuotientGroup.eq_one_iff y).2 hyA
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  exact hr.out.one_lt.ne hx

end Reduce

section CardLemmas

theorem card_comap_surj {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (E : Subgroup B) :
    Nat.card (E.comap f) = Nat.card f.ker * Nat.card E := by
  haveI : Finite B := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (E.comap f)
  have h2 := Subgroup.card_mul_index E
  have h3 := Subgroup.index_comap_of_surjective E hf
  have h4 := Subgroup.card_ker_mul_card_of_surjective hf
  rw [h3] at h1
  have hpos : 0 < E.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h4, ← h2]
  ring

end CardLemmas

section Scalars

variable {F : Type} [Field F] {m : ℕ} {C : Type} [CommGroup C]

@[expose] noncomputable def scE (e : C →* Fˣ) (m : ℕ) : C →* GL (Fin m) F :=
  (Matrix.GeneralLinearGroup.scalar (Fin m)).comp e

theorem scE_apply (e : C →* Fˣ) (z : C) :
    scE (F := F) e m z = Matrix.GeneralLinearGroup.scalar (Fin m) (e z) := rfl

theorem scE_injective (hm : 1 ≤ m) {e : C →* Fˣ} (he : Function.Injective e) :
    Function.Injective (scE (F := F) e m) := by
  intro z z' h
  apply he
  have h' : diagHom m (fun _ => e z) = diagHom m (fun _ => e z') := by
    rw [← scalar_eq_diagHom_const, ← scalar_eq_diagHom_const]
    exact h
  exact congrFun (diagHom_injective (K := F) m h') ⟨0, hm⟩

theorem scE_mem_center (e : C →* Fˣ) (z : C) :
    scE (F := F) e m z ∈ Subgroup.center (GL (Fin m) F) := by
  rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
  exact ⟨e z, rfl⟩

end Scalars

section Upper

variable {F : Type} [Field F] [Fintype F] {r m : ℕ} [hr : Fact r.Prime] {C : Type} [CommGroup C]
  [Finite C]

theorem core_elem_card_le (hperm : PermBound r m) (hr2 : r ≠ 2) (hm : 4 ≤ m) [Nontrivial C]
    (hCc : IsCyclic C) (hCr : IsPGroup r C) (e : C →* Fˣ) (he : Function.Injective e)
    (ι : Mon C m →* GL (Fin m) F) (hι : Function.Injective ι)
    (hιS : ∀ z : C, ι (monScalar C m z) = scE e m z)
    (hιdet : ∀ x : Mon C m, Odd (orderOf x) →
      Matrix.GeneralLinearGroup.det (ι x) = e (monDet x))
    (G : Subgroup (GL (Fin m) F)) (hGSL : G ≤ StatedSL m F)
    (hconj : ∀ H : Subgroup (GL (Fin m) F), H ≤ G → IsPGroup r H →
      ∃ g : GL (Fin m) F, (∀ x ∈ H, g * x * g⁻¹ ∈ G) ∧ ∀ x ∈ H, g * x * g⁻¹ ∈ ι.range)
    (C₀ : Subgroup C) (hC₀G : C₀.map (scE e m) ≤ G)
    [((C₀.map (scE e m)).subgroupOf G).Normal]
    (E : Subgroup (↥G ⧸ (C₀.map (scE e m)).subgroupOf G)) (hE : IsElemAbelian r E) :
    Nat.card E * Nat.card C₀ ≤ r ^ (m - 1) * Nat.card ↥(C₀ ⊓ Ωsc r m C) := by
  classical
  set Zr : Subgroup (GL (Fin m) F) := C₀.map (scE e m) with hZr
  set N : Subgroup ↥G := Zr.subgroupOf G with hN
  let mk : ↥G →* ↥G ⧸ N := QuotientGroup.mk' N
  let Eh : Subgroup ↥G := E.comap mk
  let Eh' : Subgroup (GL (Fin m) F) := Eh.map G.subtype
  have hm1 : 1 ≤ m := by omega
  have hNcard : Nat.card N = Nat.card C₀ := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₀G).toEquiv, hZr,
      Subgroup.card_map_of_injective (scE_injective hm1 he)]
  have hEhcard : Nat.card Eh = Nat.card N * Nat.card E := by
    rw [card_comap_surj mk (QuotientGroup.mk'_surjective N) E, QuotientGroup.ker_mk']
  have hEh'card : Nat.card Eh' = Nat.card Eh :=
    Subgroup.card_map_of_injective G.subtype_injective
  have hEpg : IsPGroup r E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨a, ha⟩ := (hCr.to_subgroup C₀).exists_card_eq
  obtain ⟨b, hb⟩ := hEpg.exists_card_eq
  have hEh'pg : IsPGroup r Eh' :=
    IsPGroup.of_card (n := a + b) (by rw [hEh'card, hEhcard, hNcard, ha, hb, pow_add])
  have hEh'G : Eh' ≤ G := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨g, hgG, hgι⟩ := hconj Eh' hEh'G hEh'pg
  let Q : Subgroup (GL (Fin m) F) := Eh'.map (MulAut.conj g).toMonoidHom
  have hQmem : ∀ q ∈ Q, ∃ y ∈ Eh', q = g * y * g⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  have hQι : Q ≤ ι.range := by
    rintro q hq
    obtain ⟨y, hy, rfl⟩ := hQmem q hq
    exact hgι y hy
  have hQG : Q ≤ G := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hQmem q hq
    exact hgG y hy
  let P : Subgroup (Mon C m) := Q.comap ι
  have hPcard : Nat.card P = Nat.card Eh' := by
    have h1 : (P.map ι) = Q := Subgroup.map_comap_eq_self hQι
    have h2 : Nat.card (P.map ι) = Nat.card P := Subgroup.card_map_of_injective hι
    have h3 : Nat.card Q = Nat.card Eh' :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [← h2, h1, h3]
  have hlift : ∀ x ∈ P, ∃ y : ↥G, y ∈ Eh ∧ ι x = g * (y : GL (Fin m) F) * g⁻¹ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hQmem (ι x) hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', hy', hxy⟩
  have hscc : ∀ z : C, ∀ q : GL (Fin m) F, q * scE e m z * q⁻¹ = scE e m z := by
    intro z q
    have := Subgroup.mem_center_iff.1 (scE_mem_center (F := F) (m := m) e z) q
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hpowP : ∀ x ∈ P, x ^ r ∈ C₀.map (monScalar C m) := by
    intro x hx
    obtain ⟨y, hyE, hxy⟩ := hlift x hx
    have h1 : (mk y) ^ r = 1 := hE.2 _ hyE
    have h2 : y ^ r ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact h1
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h2)
    refine Subgroup.mem_map.2 ⟨z, hz, hι ?_⟩
    have h3 : (y : GL (Fin m) F) ^ r = scE e m z := by
      rw [← Subgroup.coe_pow]
      exact hzy.symm
    rw [hιS, map_pow, hxy, conj_pow, h3, hscc]
  have hdetP : ∀ x ∈ P, monDet x = 1 := by
    intro x hx
    obtain ⟨y, hyE, hxy⟩ := hlift x hx
    have hord : Odd (orderOf x) := by
      obtain ⟨k, hk⟩ := hEh'pg ⟨(y : GL (Fin m) F), ⟨y, hyE, rfl⟩⟩
      have hk' : (y : GL (Fin m) F) ^ (r ^ k) = 1 := congrArg Subtype.val hk
      have hx1 : x ^ (r ^ k) = 1 := by
        apply hι
        rw [map_pow, hxy, conj_pow, hk', mul_one, mul_inv_cancel, map_one]
      have hdvd : orderOf x ∣ r ^ k := orderOf_dvd_of_pow_eq_one hx1
      exact Odd.of_dvd_nat ((hr.out.odd_of_ne_two hr2).pow) hdvd
    have hdet1 : Matrix.GeneralLinearGroup.det (ι x) = 1 := by
      have hιx : ι x ∈ G := by
        rw [hxy]
        exact hgG _ ⟨y, hyE, rfl⟩
      have h2 := hGSL hιx
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker] at h2
      exact h2
    rw [hιdet x hord] at hdet1
    exact he (hdet1.trans (map_one e).symm)
  have hcommP : ∀ x ∈ P, ∀ x' ∈ P, ⁅x, x'⁆ ∈ C₀.map (monScalar C m) := by
    intro x hx x' hx'
    obtain ⟨y, hyE, hxy⟩ := hlift x hx
    obtain ⟨y', hy'E, hxy'⟩ := hlift x' hx'
    haveI := hE.1
    have h1 : mk y * mk y' = mk y' * mk y :=
      congrArg Subtype.val (mul_comm' (⟨mk y, hyE⟩ : E) ⟨mk y', hy'E⟩)
    have h2 : ⁅y, y'⁆ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact (map_commutatorElement mk y y').trans (commutatorElement_eq_one_iff_mul_comm.2 h1)
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h2)
    refine Subgroup.mem_map.2 ⟨z, hz, hι ?_⟩
    have h3 : ⁅(y : GL (Fin m) F), (y' : GL (Fin m) F)⁆ = scE e m z := by
      exact hzy.symm
    rw [hιS, map_commutatorElement, hxy, hxy']
    have h4 := map_commutatorElement (MulAut.conj g) (y : GL (Fin m) F) (y' : GL (Fin m) F)
    simp only [MulAut.conj_apply] at h4
    rw [← h4, h3, hscc]
  have hmon := monCore_of_perm hperm hm hCc hCr C₀ P hdetP hpowP hcommP
  calc Nat.card E * Nat.card C₀ = Nat.card P := by
        rw [hPcard, hEh'card, hEhcard, hNcard]
        ring
    _ ≤ r ^ (m - 1) * Nat.card ↥(C₀ ⊓ Ωsc r m C) := hmon

theorem scalarGL_injective (hm : 1 ≤ m) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) := by
  intro u u' h
  have h' : diagHom m (fun _ => u) = diagHom m (fun _ => u') := by
    rw [← scalar_eq_diagHom_const, ← scalar_eq_diagHom_const]
    exact h
  exact congrFun (diagHom_injective (K := F) m h') ⟨0, hm⟩

open scoped Classical in
theorem pRank_quot_core (hperm : PermBound r m) (hr2 : r ≠ 2) (hm : 4 ≤ m) [Nontrivial C]
    (hCc : IsCyclic C) (hCr : IsPGroup r C) (e : C →* Fˣ) (he : Function.Injective e)
    (hCmax : ∀ u : Fˣ, (∃ k : ℕ, u ^ (r ^ k) = 1) → u ∈ e.range)
    (ι : Mon C m →* GL (Fin m) F) (hι : Function.Injective ι)
    (hιS : ∀ z : C, ι (monScalar C m z) = scE e m z)
    (hιdet : ∀ x : Mon C m, Odd (orderOf x) →
      Matrix.GeneralLinearGroup.det (ι x) = e (monDet x))
    (G : Subgroup (GL (Fin m) F)) (hGSL : G ≤ StatedSL m F)
    (hdiag : ∀ t : Fin m → C, ∏ i, t i = 1 → diagHom m (fun i => e (t i)) ∈ G)
    (hconj : ∀ H : Subgroup (GL (Fin m) F), H ≤ G → IsPGroup r H →
      ∃ g : GL (Fin m) F, (∀ x ∈ H, g * x * g⁻¹ ∈ G) ∧ ∀ x ∈ H, g * x * g⁻¹ ∈ ι.range)
    (Z : Subgroup (GL (Fin m) F)) (hZG : Z ≤ G) (hZsc : Z ≤ StatedScalars (Fin m) F)
    [(Z.subgroupOf G).Normal] :
    CFSG.Open.pRank r (⊤ : Subgroup (↥G ⧸ Z.subgroupOf G)) =
      m - 1 - (if ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Z then 1 else 0) := by
  have hm1 : 1 ≤ m := by omega
  set C₀ : Subgroup C := Z.comap (scE e m) with hC₀
  set Zr : Subgroup (GL (Fin m) F) := C₀.map (scE e m) with hZr
  have hmemC₀ : ∀ z : C, z ∈ C₀ ↔ Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Z :=
    fun z => Iff.rfl
  have hZrZ : Zr ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  have hZrG : Zr ≤ G := hZrZ.trans hZG
  have hZrsc : Zr ≤ StatedScalars (Fin m) F := by
    rintro _ ⟨z, -, rfl⟩
    exact ⟨e z, rfl⟩
  haveI hZrN : (Zr.subgroupOf G).Normal := by
    apply Subgroup.normal_of_le_center
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxc : (x : GL (Fin m) F) ∈ Subgroup.center (GL (Fin m) F) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact hZrsc (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_center_iff.1 hxc (y : GL (Fin m) F)
  have hred : CFSG.Open.pRank r (⊤ : Subgroup (↥G ⧸ Z.subgroupOf G)) =
      CFSG.Open.pRank r (⊤ : Subgroup (↥G ⧸ Zr.subgroupOf G)) := by
    refine pRank_quot_eq_of_le (Zr.subgroupOf G) (Z.subgroupOf G) (fun x hx => hZrZ hx) ?_ ?_
    · intro x
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
      obtain ⟨k, hk⟩ := hCr z
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      change ((x : ↥G) : GL (Fin m) F) ^ (r ^ k) = 1
      rw [← hzx, ← map_pow]
      have : z ^ (r ^ k) = 1 := hk
      rw [this, map_one]
    · intro y hy hyk
      obtain ⟨k, hk⟩ := hyk
      have hyZ : (y : GL (Fin m) F) ∈ Z := Subgroup.mem_subgroupOf.1 hy
      obtain ⟨u, hu⟩ := hZsc hyZ
      have hk' : (y : GL (Fin m) F) ^ (r ^ k) = 1 := by
        have := congrArg (fun w : ↥G => (w : GL (Fin m) F)) hk
        simpa using this
      have hu' : u ^ (r ^ k) = 1 := by
        apply scalarGL_injective (F := F) hm1
        rw [map_pow, hu, hk', map_one]
      obtain ⟨z, hz⟩ := hCmax u ⟨k, hu'⟩
      have hzC₀ : z ∈ C₀ := by
        rw [hmemC₀, hz, hu]
        exact hyZ
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨z, hzC₀, by
        rw [scE_apply, hz, hu]⟩)
  rw [hred]
  have hδ : (∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Z) ↔
      (∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Zr) := by
    refine ⟨fun h z => Subgroup.mem_map.2 ⟨z, (hmemC₀ z).2 (h z), rfl⟩, fun h z => hZrZ (h z)⟩
  apply le_antisymm
  ·
    refine pRank_le hr.out.one_lt fun E _ hE => ?_
    have key := core_elem_card_le hperm hr2 hm hCc hCr e he ι hι hιS hιdet G hGSL hconj C₀ hZrG
      E hE
    have hC₀pos : 0 < Nat.card C₀ := Nat.card_pos
    by_cases htop : ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Z
    · rw [if_pos htop]
      have hC₀top : C₀ = ⊤ := Subgroup.eq_top_iff' _ |>.2 fun z => (hmemC₀ z).2 (htop z)
      have h1 : Nat.card ↥(C₀ ⊓ Ωsc r m C) ≤ Nat.card (powMonoidHom r : C →* C).range := by
        apply Subgroup.card_le_of_le
        rintro z ⟨-, s, -, hs⟩
        exact ⟨s ⟨0, hm1⟩, by simpa [powMonoidHom_apply] using hs ⟨0, hm1⟩⟩
      have hrk : r ≤ Nat.card (powMonoidHom r : C →* C).ker := by
        obtain ⟨n, hn, hnc⟩ := hCr.nontrivial_iff_card.1 inferInstance
        exact le_card_pow_ker (hnc ▸ dvd_pow_self r hn.ne')
      have h2 : r * Nat.card (powMonoidHom r : C →* C).range ≤ Nat.card C₀ := by
        rw [hC₀top, Subgroup.card_top, ← Subgroup.card_ker_mul_card_range (powMonoidHom r : C →* C)]
        exact Nat.mul_le_mul_right _ hrk
      have h3 : Nat.card E * Nat.card C₀ * r ≤ r ^ (m - 1) * Nat.card C₀ := by
        calc Nat.card E * Nat.card C₀ * r ≤ r ^ (m - 1) * Nat.card ↥(C₀ ⊓ Ωsc r m C) * r :=
              Nat.mul_le_mul_right _ key
          _ = r ^ (m - 1) * (r * Nat.card ↥(C₀ ⊓ Ωsc r m C)) := by ring
          _ ≤ r ^ (m - 1) * Nat.card C₀ :=
              Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ h1).trans h2)
      have h4 : Nat.card E * r ≤ r ^ (m - 1) := by
        have : Nat.card E * r * Nat.card C₀ ≤ r ^ (m - 1) * Nat.card C₀ := by
          calc Nat.card E * r * Nat.card C₀ = Nat.card E * Nat.card C₀ * r := by ring
            _ ≤ _ := h3
        exact Nat.le_of_mul_le_mul_right this hC₀pos
      have h5 : r ^ (m - 1) = r * r ^ (m - 1 - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h5] at h4
      have h6 : Nat.card E ≤ r ^ (m - 1 - 1) := by
        have : Nat.card E * r ≤ r ^ (m - 1 - 1) * r := by
          calc Nat.card E * r ≤ r * r ^ (m - 1 - 1) := h4
            _ = _ := by ring
        exact Nat.le_of_mul_le_mul_right this hr.out.pos
      have : m - 1 - 1 = m - 1 - 1 := rfl
      exact h6
    · rw [if_neg htop]
      have h1 : Nat.card ↥(C₀ ⊓ Ωsc r m C) ≤ Nat.card C₀ :=
        Subgroup.card_le_of_le inf_le_left
      have h2 : Nat.card E * Nat.card C₀ ≤ r ^ (m - 1) * Nat.card C₀ :=
        key.trans (Nat.mul_le_mul_left _ h1)
      have := Nat.le_of_mul_le_mul_right h2 hC₀pos
      simpa using this
  ·
    have h := toral_lower_bound hm1 hCc hCr e he G hGSL hdiag Zr hZrG hZrsc
    have hif : (if ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Zr then 1 else 0) =
        (if ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Z then 1 else 0) := by
      simp only [hδ]
    rwa [hif] at h

end Upper

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
