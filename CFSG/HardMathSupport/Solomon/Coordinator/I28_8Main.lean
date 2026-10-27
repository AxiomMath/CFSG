module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Hall
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8L34
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28_8
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.Quasithin.Background.G116IIIFStar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7K28

@[expose] noncomputable def piHom (X : Type) [Group X] :
    X →* (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore 3 ↥(⊤ : Subgroup X)) :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(⊤ : Subgroup X))).comp
    (Subgroup.topEquiv (G := X)).symm.toMonoidHom

theorem piHom_apply {X : Type} [Group X] (x : X) :
    piHom X x = QuotientGroup.mk (⟨x, trivial⟩ : ↥(⊤ : Subgroup X)) := rfl

theorem piHom_surjective (X : Type) [Group X] : Function.Surjective (piHom X) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x, rfl⟩

theorem ker_piHom (X : Type) [Group X] [Finite X] : (piHom X).ker = oPrime3 X := by
  ext x
  rw [MonoidHom.mem_ker, piHom_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h; exact ⟨⟨x, trivial⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, trivial⟩ := Subtype.ext hyx
    exact this ▸ hy

theorem barX_eq_map {X : Type} [Group X] (A : Subgroup X) :
    barX 3 (⊤ : Subgroup X) A = A.map (piHom X) := by
  ext y
  constructor
  · rintro ⟨⟨x, hx⟩, hxA, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.1 hxA, rfl⟩
  · rintro ⟨x, hxA, rfl⟩
    exact ⟨⟨x, trivial⟩, Subgroup.mem_subgroupOf.2 hxA, rfl⟩

theorem eq_one_of_pow_three {Y : Type*} [Group Y] {P : Subgroup Y} (hP : IsPGroup 2 P) {c : Y}
    (hc : c ∈ P) (h3 : c ^ 3 = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hP ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at hj
  have hd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using hj
  · exfalso
    have : 2 ∣ 3 := (dvd_pow_self 2 hjpos.ne').trans (hj ▸ hd)
    omega

theorem kbar_normal {Y : Type} [Group Y] [Finite Y] {E T B : Subgroup Y}
    (hE : CFSG.Open.IsComponentOf E ⊤) (hZ : ∀ z ∈ E, (∀ e ∈ E, z * e = e * z) → z = 1)
    (hT : IsPGroup 2 T) (hB3 : ∀ x ∈ B, x ^ 3 = 1) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBT : B ≤ Subgroup.normalizer (T : Set Y)) {b : Y} (hbB : b ∈ B) (hbE : b ∈ E) (hb1 : b ≠ 1)
    (hY : E ⊔ T ⊔ B = ⊤) : E.Normal := by
  have hE' : CFSG.GorensteinWalter.IsComponentOf E ⊤ := (CFSG.Adapters.isComponentOf_top_iff E).1 hE
  have key : ∀ g : Y, ∀ P : Subgroup Y, IsPGroup 2 P → g * b * g⁻¹ * b⁻¹ ∈ P →
      g ∈ Subgroup.normalizer (E : Set Y) := by
    intro g P hP hc
    set F : Subgroup Y := E.map (MulAut.conj g).toMonoidHom with hF
    have hFcomp : CFSG.Open.IsComponentOf F ⊤ := CFSG.Quasithin.G11.open_isComponentOf_top_map_conj hE g
    have hF' : CFSG.GorensteinWalter.IsComponentOf F ⊤ := (CFSG.Adapters.isComponentOf_top_iff F).1 hFcomp
    by_cases hFE : F = E
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have : g * x * g⁻¹ ∈ F := ⟨x, hx, by simp [MulAut.conj_apply]⟩
        rwa [hFE] at this
      · intro hx
        have hx' : g * x * g⁻¹ ∈ F := hFE.symm ▸ hx
        obtain ⟨y, hy, hyx⟩ := hx'
        have : y = x := by
          simpa [MulAut.conj_apply] using hyx
        exact this ▸ hy
    · exfalso
      have hcomm := CFSG.GorensteinWalter.component_commute_of_ne hF' hE' hFE
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      have hb'F : g * b * g⁻¹ ∈ F := ⟨b, hbE, by simp [MulAut.conj_apply]⟩
      have hcb : ∀ e ∈ E, e * (g * b * g⁻¹) = (g * b * g⁻¹) * e := fun e he =>
        Subgroup.mem_centralizer_iff.1 (hcomm hb'F) e he
      have hcomm2 : Commute (g * b * g⁻¹) b⁻¹ :=
        (hcb b⁻¹ (E.inv_mem hbE)).symm
      have hc3 : (g * b * g⁻¹ * b⁻¹) ^ 3 = 1 := by
        rw [hcomm2.mul_pow]
        have h1 : (g * b * g⁻¹) ^ 3 = 1 := by
          have := map_pow (MulAut.conj g) b 3
          simp only [MulAut.conj_apply] at this
          rw [← this, hB3 b hbB]; simp
        rw [h1, inv_pow, hB3 b hbB]; simp
      have hc1 := eq_one_of_pow_three hP hc hc3
      have hbb : g * b * g⁻¹ = b := by
        have := congrArg (· * b) hc1
        simpa using this
      have hbF : b ∈ F := hbb ▸ hb'F
      exact hb1 (hZ b hbE (fun e he => by have := hcb e he; rw [hbb] at this; exact this.symm))
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hY]
  refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
  · intro g hg
    refine key g T hT ?_
    have : g * b * g⁻¹ * b⁻¹ = g * (b * g⁻¹ * b⁻¹) := by group
    rw [this]
    exact mul_mem hg ((Subgroup.mem_normalizer_iff.1 (hBT hbB) g⁻¹).1 (T.inv_mem hg))
  · intro g hg
    refine key g ⊥ (IsPGroup.of_card (n := 0) (by simp)) ?_
    rw [hBc g hg b hbB, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem exists_mul_mem_normalizer {X : Type} [Group X] [Finite X] {W T : Subgroup X}
    (hT2 : IsPGroup 2 T) (hTW : T ≤ W) (hidx : ¬ 2 ∣ T.relIndex W) {g : X}
    (hg : g ∈ Subgroup.normalizer (W : Set X)) :
    ∃ u ∈ W, u * g ∈ Subgroup.normalizer (T : Set X) := by
  classical
  set G₂ : Subgroup X := Subgroup.normalizer (W : Set X) with hG₂
  have hWG : W ≤ G₂ := Subgroup.le_normalizer
  have hnorm : (W.subgroupOf G₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWG).2 le_rfl
  have hPN : T.subgroupOf G₂ ≤ W.subgroupOf G₂ := fun x hx => hTW hx
  have hP2 : IsPGroup 2 (T.subgroupOf G₂) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe (hTW.trans hWG)).symm
  have hrel : ¬ 2 ∣ (T.subgroupOf G₂).relIndex (W.subgroupOf G₂) := by
    rwa [Subgroup.relIndex_subgroupOf hWG]
  have hfr := frattini_ker hPN hP2 hrel
  have hgG : (⟨g⁻¹, G₂.inv_mem hg⟩ : ↥G₂) ∈
      Subgroup.normalizer ((T.subgroupOf G₂ : Subgroup ↥G₂) : Set ↥G₂) ⊔ W.subgroupOf G₂ :=
    hfr ▸ Subgroup.mem_top _
  obtain ⟨m, hm, w, hw, hmw⟩ := Subgroup.mem_sup_of_normal_right.1 hgG
  have hw' : (w : X) ∈ W := hw
  refine ⟨(w : X), hw', ?_⟩
  have h1 : (w : X) * g = ((m : X))⁻¹ := by
    have := congrArg Subtype.val hmw
    simp only [Subgroup.coe_mul] at this
    have h2 : g = (w : X)⁻¹ * (m : X)⁻¹ := by
      rw [← mul_inv_rev, this]; simp
    rw [h2]; group
  rw [h1]
  have hconj : ∀ n : ↥G₂, n ∈ Subgroup.normalizer ((T.subgroupOf G₂ : Subgroup ↥G₂) : Set ↥G₂) →
      ∀ x ∈ T, (n : X) * x * (n : X)⁻¹ ∈ T := by
    intro n hn x hx
    have hxG : x ∈ G₂ := hWG (hTW hx)
    have := (Subgroup.mem_normalizer_iff.1 hn ⟨x, hxG⟩).1 hx
    exact this
  have hmN : (m : X) ∈ Subgroup.normalizer (T : Set X) :=
    mem_normalizer_of_conj_mem' (hconj m hm) (fun x hx => by
      have := hconj m⁻¹ (Subgroup.inv_mem _ hm) x hx
      simpa using this)
  exact Subgroup.inv_mem _ hmN

theorem centralizer_map_le_map_normalizer {X D : Type} [Group X] [Finite X] [Group D]
    {N T : Subgroup X} [hNn : N.Normal] (π : X →* D) (hker : π.ker = N)
    (hπ : Function.Surjective π) (hT2 : IsPGroup 2 T) (hPN : ¬ 2 ∣ (T ⊓ N).relIndex N) :
    Subgroup.centralizer ((T.map π : Subgroup D) : Set D) ≤
      (Subgroup.normalizer (T : Set X)).map π := by
  intro y hy
  obtain ⟨g, rfl⟩ := hπ y
  have hker1 : ∀ n ∈ N, π n = 1 := fun n hn => MonoidHom.mem_ker.1 (hker ▸ hn)
  set W : Subgroup X := T ⊔ N with hW
  have hTN : T ≤ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hpre : ∀ z : X, π z ∈ T.map π → z ∈ W := by
    rintro z ⟨t, ht, hte⟩
    have h0 : π (t⁻¹ * z) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
    have hn : t⁻¹ * z ∈ N := hker ▸ MonoidHom.mem_ker.2 h0
    have : z = t * (t⁻¹ * z) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hn)
  have hπW : ∀ x ∈ W, π x ∈ T.map π := by
    intro x hx
    obtain ⟨t, ht, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    exact ⟨t, ht, by rw [map_mul, hker1 n hn, mul_one]⟩
  have hgW : g ∈ Subgroup.normalizer (W : Set X) := by
    refine mem_normalizer_of_conj_mem' (fun x hx => ?_) (fun x hx => ?_)
    · apply hpre
      have h1 := Subgroup.mem_centralizer_iff.1 hy (π x) (hπW x hx)
      have h2 : π g * π x * (π g)⁻¹ = π x := by
        rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
      rw [map_mul, map_mul, map_inv, h2]
      exact hπW x hx
    · apply hpre
      have h1 := Subgroup.mem_centralizer_iff.1 hy (π x) (hπW x hx)
      have h2 : (π g)⁻¹ * π x * π g = π x := by
        rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [map_mul, map_mul, map_inv, h2]
      exact hπW x hx
  have hTW : T ≤ W := le_sup_left
  have hidx : ¬ 2 ∣ T.relIndex W := by
    rw [hW, relIndex_sup_of_le_normalizer hTN]; exact hPN
  obtain ⟨u, hu, hug⟩ := exists_mul_mem_normalizer hT2 hTW hidx hgW
  obtain ⟨t, ht, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu
  refine ⟨n * g, ?_, ?_⟩
  · have : n * g = t⁻¹ * (t * n * g) := by group
    rw [this]
    exact mul_mem (Subgroup.inv_mem _ (Subgroup.le_normalizer ht)) hug
  · rw [map_mul, hker1 n hn, one_mul]

theorem mem_normalizer_sup_of_normal {X : Type*} [Group X] {T U : Subgroup X} [hU : U.Normal] {g : X}
    (hg : g ∈ Subgroup.normalizer (T : Set X)) : g ∈ Subgroup.normalizer ((T ⊔ U : Subgroup X) : Set X) := by
  have key : ∀ {g : X}, g ∈ Subgroup.normalizer (T : Set X) → ∀ x ∈ T ⊔ U,
      g * x * g⁻¹ ∈ T ⊔ U := by
    intro g hg x hx
    obtain ⟨t, ht, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    have : g * (t * o) * g⁻¹ = (g * t * g⁻¹) * (g * o * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 hg t).1 ht) (hU.conj_mem o ho g)
  exact mem_normalizer_of_conj_mem' (key hg) (fun x hx => by
    simpa using key (inv_mem hg) x hx)

theorem pCore_le_of_isMax {X : Type} [Group X] [Finite X] {B T U : Subgroup X} [U.Normal]
    (hU2 : IsPGroup 2 U) (hT : IsMaxBInvariantTwo B T) : U ≤ T := by
  obtain ⟨hT2, hBT, hmax⟩ := hT
  have h1 : T ⊔ U = T :=
    hmax (T ⊔ U) (hT2.to_sup_of_normal_right hU2) (fun b hb => mem_normalizer_sup_of_normal (hBT hb))
      le_sup_left
  exact h1 ▸ le_sup_right

theorem isLThreeFour_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsLThreeFour A) : IsLThreeFour B := by
  obtain ⟨F, hF, hfin, hc, ⟨φ⟩⟩ := h
  exact ⟨F, hF, hfin, hc, ⟨e.symm.trans φ⟩⟩

theorem center_trivial_of_isLThreeFour {A : Type} [Group A] (h : IsLThreeFour A) :
    ∀ z : A, (∀ e : A, z * e = e * z) → z = 1 := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := exists_equiv_projectiveSL' h
  intro z hz
  have hc : φ z ∈ Subgroup.center (projectiveSL 3 k) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨e, rfl⟩ := φ.surjective w
    rw [← map_mul, ← map_mul, hz e]
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk,
    Subgroup.mem_bot] at hc
  exact φ.injective (hc.trans (map_one φ).symm)

theorem map_normalizer_le {X D : Type*} [Group X] [Group D] (π : X →* D) {T : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (T : Set X)) :
    π g ∈ Subgroup.normalizer ((T.map π : Subgroup D) : Set D) := by
  have key : ∀ {g : X}, g ∈ Subgroup.normalizer (T : Set X) → ∀ y ∈ T.map π,
      π g * y * (π g)⁻¹ ∈ T.map π := by
    rintro g hg _ ⟨t, ht, rfl⟩
    exact ⟨g * t * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg t).1 ht, by simp⟩
  exact mem_normalizer_of_conj_mem' (key hg) (fun y hy => by
    simpa using key (inv_mem hg) y hy)

theorem input28_8Offending_of (h : Th1FactorizationTwoSeven) (hL34 : L34Facts) :
    Input28_8Offending := by
  intro X _ _ hK hC K T B hKc hL hB hT hJ hX h9
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  have hNn : (oPrime3 X).Normal := oPrime3_normal
  have hPN := not_two_dvd_relIndex_inf hBp hT
  have hker := ker_piHom X
  have hsurj := piHom_surjective X
  have hUeq : CFSG.pCore 2 X = CFSG.Open.pCore 2 X := CFSG.pCore_eq_open X 2
  have hUn : (CFSG.Open.pCore 2 X).Normal := CFSG.pCore_normal
  have hU2 : IsPGroup 2 (CFSG.Open.pCore 2 X) := CFSG.pCore_isPGroup
  have hUT : CFSG.Open.pCore 2 X ≤ T := pCore_le_of_isMax hU2 hT
  rw [barX_eq_map, barX_eq_map, barX_eq_map] at hX
  rw [barX_eq_map, barX_eq_map] at h9
  have hKsub : CFSG.Open.IsSubnormal K ⊤ := hKc.2.1
  have hLE : IsLThreeFour ↥(K.map (piHom X)) := by
    have := LocalBalance.Lemma512Ns.barXEquiv Nat.prime_three hKsub
    rw [barX_eq_map] at this
    exact isLThreeFour_of_equiv this hL
  have hcomp : CFSG.Open.IsComponentOf (K.map (piHom X)) ⊤ := by
    have : CFSG.Open.IsComponentOf (barX 3 (⊤ : Subgroup X) K) ⊤ := hKc.2.2.1
    rwa [barX_eq_map] at this
  have := hNn
  set E := K.map (piHom X) with hE
  set T' := T.map (piHom X) with hT'
  set B' := B.map (piHom X) with hB'
  have hT'2 : IsPGroup 2 T' := hT.1.map (piHom X)
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩; rw [← map_pow, hB.2 y hy, map_one]
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    have := congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact congrArg _ this
  have hBT' : B' ≤ Subgroup.normalizer (T' : Set _) := by
    rintro _ ⟨b, hb, rfl⟩; exact map_normalizer_le _ (hT.2.1 hb)
  obtain ⟨b, hb⟩ : ∃ b : ↥(B' ⊓ E), b ≠ 1 :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (by intro h; rw [h] at h9; simp at h9)
  have hEn : E.Normal :=
    kbar_normal hcomp (fun z hz hzc => by
        have := center_trivial_of_isLThreeFour hLE ⟨z, hz⟩ (fun e => Subtype.ext (hzc e e.2))
        exact congrArg Subtype.val this)
      hT'2 hB'3 hB'c hBT' b.2.1 b.2.2 (fun h => hb (Subtype.ext h)) hX
  have hcent := centralizer_map_le_map_normalizer (N := oPrime3 X) (piHom X) hker hsurj hT.1 hPN
  rcases hL34 _ E T' B' hEn hLE hT'2 hBT' h9 with hcen | ⟨Q, hQE, hQ7, hTQ, ⟨t, ht, hinv⟩, hgen⟩
  · refine ⟨Finset.univ, by decide, fun i _ => ?_⟩
    rw [barX_eq_map, barX_eq_map]
    exact hcen.trans (hcent.trans (Subgroup.map_mono
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.normalizer_le_normalizer_tripleOf T i)))
  · obtain ⟨t0, ht0, rfl⟩ := ht
    have hQr : Q ≤ (piHom X).range := by
      rw [MonoidHom.range_eq_top.2 hsurj]; exact le_top
    obtain ⟨s, hs, hsQ⟩ := two_cover_of_twoSeven h hT.1 hPN hUn hU2 hUT hC (piHom X) hker Q hQ7
      hQr hTQ ⟨t0, ht0, hinv⟩
    refine ⟨s, hs, fun i hi => ?_⟩
    rw [barX_eq_map, barX_eq_map]
    refine (le_of_eq hgen.symm).trans (sup_le ?_ (hsQ i hi))
    exact inf_le_left.trans (hcent.trans (Subgroup.map_mono
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.normalizer_le_normalizer_tripleOf T i)))

theorem input28_8_of_twoSeven (h : Th1FactorizationTwoSeven) :
    Input28_8 :=
  input28_8_of_offending (input28_8Offending_of h l34Facts_holds)

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
