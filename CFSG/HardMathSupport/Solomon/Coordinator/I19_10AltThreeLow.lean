module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Subgroup

section Join
variable {M : Type*} [Group M]


private theorem i1910a3_join_comm_aux {A B : Subgroup M} (h : A ≤ centralizer (B : Set M)) :
    ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
  (h m.2 n n.2).symm

private theorem i1910a3_join_range {A B : Subgroup M} (h : A ≤ centralizer (B : Set M)) :
    (MonoidHom.noncommCoprod A.subtype B.subtype (i1910a3_join_comm_aux h)).range = A ⊔ B := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (i1910a3_join_comm_aux h)
  rwa [Subgroup.range_subtype, Subgroup.range_subtype] at hr

private theorem i1910a3_join_facts {A B : Subgroup M} {p : ℕ} (h : A ≤ centralizer (B : Set M))
    (hAB : A ⊓ B = ⊥) (hA : IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1)
    (hB : IsMulCommutative B ∧ ∀ x ∈ B, x ^ p = 1) :
    IsMulCommutative (A ⊔ B : Subgroup M) ∧ (∀ x ∈ A ⊔ B, x ^ p = 1) ∧
      (Finite A → Finite B → Nat.card (A ⊔ B : Subgroup M) = Nat.card A * Nat.card B) := by
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype (i1910a3_join_comm_aux h) with hφ
  have hrange := i1910a3_join_range h
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hAB
  obtain ⟨hAc, hAe⟩ := hA
  obtain ⟨hBc, hBe⟩ := hB
  refine ⟨⟨⟨?_⟩⟩, ?_, ?_⟩
  · intro x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rw [← hrange] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    apply Subtype.ext
    show φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (congrArg Subtype.val (hAc.is_comm.comm u.1 v.1))
    · exact Subtype.ext (congrArg Subtype.val (hBc.is_comm.comm u.2 v.2))
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ p = 1 := Prod.ext (Subtype.ext (hAe _ u.1.2 |> fun h' => by simpa using h'))
      (Subtype.ext (hBe _ u.2.2 |> fun h' => by simpa using h'))
    rw [this, map_one]
  · intro hAf hBf
    have e : (A × B) ≃ (A ⊔ B : Subgroup M) :=
      (MonoidHom.ofInjective hinj).toEquiv.trans (MulEquiv.subgroupCongr hrange).toEquiv
    rw [← Nat.card_prod, Nat.card_congr e]

theorem i1910a3_exists_elemAbelian_join
    {M : Type*} [Group M] [Finite M] {p : ℕ} (_hp : p.Prime)
    {I : Type*} [Fintype I] (Y E : I → Subgroup M) (C0 : Subgroup M) (q : ℕ)
    (hYcomm : ∀ i j, i ≠ j → Y i ≤ Subgroup.centralizer (Y j : Set M))
    (hEY : ∀ i, E i ≤ Y i)
    (hYz : ∀ i, ∀ y ∈ Y i, (∀ y' ∈ Y i, y * y' = y' * y) → y = 1)
    (hCY : ∀ i, C0 ≤ Subgroup.centralizer (Y i : Set M))
    (hC : IsMulCommutative C0 ∧ ∀ x ∈ C0, x ^ p = 1)
    (hE : ∀ i, IsMulCommutative (E i) ∧ (∀ x ∈ E i, x ^ p = 1) ∧ Nat.card (E i) = p ^ q) :
    ∃ P : Subgroup M, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card C0 * p ^ (q * Fintype.card I) ∧
      ∀ T : Subgroup M, C0 ≤ Subgroup.normalizer (T : Set M) →
        (∀ i, E i ≤ Subgroup.normalizer (T : Set M)) → P ≤ Subgroup.normalizer (T : Set M) := by
  classical
  have key : ∀ s : Finset I, IsMulCommutative (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ∧
      (∀ x ∈ (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M), x ^ p = 1) ∧
      Nat.card (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) = Nat.card C0 * p ^ (q * s.card) ∧
      ∀ j ∉ s, (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ≤ centralizer (Y j : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset I), E i : Subgroup M) = ⊥ := by simp
      rw [h0, sup_bot_eq]
      exact ⟨hC.1, hC.2, by simp, fun j _ => hCY j⟩
    | insert j s hj ih =>
      obtain ⟨ihc, ihe, ihn, ihy⟩ := ih
      have hJ : (C0 ⊔ ⨆ i ∈ insert j s, E i : Subgroup M) =
          (C0 ⊔ ⨆ i ∈ s, E i) ⊔ E j := by
        rw [Finset.iSup_insert, sup_comm (E j), sup_assoc]
      have hle : (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ≤ centralizer (E j : Set M) :=
        (ihy j hj).trans (Subgroup.centralizer_le (hEY j))
      have hinf : (C0 ⊔ ⨆ i ∈ s, E i : Subgroup M) ⊓ E j = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_bot]
        refine hYz j y (hEY j hy.2) fun y' hy' => ?_
        exact (ihy j hj hy.1 y' hy').symm
      obtain ⟨hc, he, hn⟩ := i1910a3_join_facts hle hinf ⟨ihc, ihe⟩ ⟨(hE j).1, (hE j).2.1⟩
      rw [hJ]
      refine ⟨hc, he, ?_, ?_⟩
      · rw [hn inferInstance inferInstance, ihn, (hE j).2.2, Finset.card_insert_of_notMem hj]
        rw [mul_add_one, pow_add, mul_assoc]
      · intro i hi
        rw [Finset.mem_insert, not_or] at hi
        exact sup_le (ihy i hi.2) ((hEY j).trans (hYcomm j i (Ne.symm hi.1)))
  obtain ⟨hc, he, hn, -⟩ := key Finset.univ
  refine ⟨C0 ⊔ ⨆ i ∈ (Finset.univ : Finset I), E i, hc, he, ?_, ?_⟩
  · rw [hn, Finset.card_univ]
  · intro T hC0 hET
    exact sup_le hC0 (iSup₂_le fun i _ => hET i)


end Join

section Lift
open Subgroup

variable {M : Type*} [Group M]


private theorem i1910a3_card_comap_mk (O : Subgroup M) [O.Normal] (K : Subgroup (M ⧸ O)) :
    Nat.card (K.comap (QuotientGroup.mk' O)) = Nat.card O * Nat.card K :=
  QuotientGroup.card_preimage_mk O (K : Set (M ⧸ O))

private theorem i1910a3_le_normalizer_of_forward {H K : Subgroup M}
    (h : ∀ x ∈ K, ∀ y ∈ H, x * y * x⁻¹ ∈ H) : K ≤ normalizer (H : Set M) := by
  intro x hx
  rw [mem_normalizer_iff]
  refine fun y => ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

private theorem i1910a3_exists_normalized_two_sylow [Finite M] {p : ℕ} (hp : p.Prime) {V K : Subgroup M}
    (hK : K ≤ normalizer (V : Set M)) (hKp : IsPGroup p K) (hnd : ¬ p ∣ Nat.card V)
    (hV2 : 2 ∣ Nat.card V) :
    ∃ S : Subgroup M, S ≠ ⊥ ∧ IsPGroup 2 S ∧ K ≤ normalizer (S : Set M) := by
  classical
  have := Fact.mk hp
  let f : K →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hK)
  let _ : MulDistribMulAction K V := MulDistribMulAction.compHom V f
  have hcard : Nat.card (Sylow 2 V) ∣ Nat.card V :=
    (Sylow.card_dvd_index (default : Sylow 2 V)).trans (Subgroup.index_dvd_card _)
  have hnd' : ¬ p ∣ Nat.card (Sylow 2 V) := fun h => hnd (h.trans hcard)
  have hfix : (MulAction.fixedPoints K (Sylow 2 V)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hmod := hKp.card_modEq_card_fixedPoints (Sylow 2 V)
    rw [hne] at hmod
    have h0 : Nat.card (↥(∅ : Set (Sylow 2 V))) = 0 := by simp
    rw [h0] at hmod
    exact hnd' ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨Q, hQ⟩ := hfix
  rw [MulAction.mem_fixedPoints] at hQ
  refine ⟨(Q : Subgroup V).map V.subtype, ?_, ?_, ?_⟩
  · intro h
    exact Q.ne_bot_of_dvd_card hV2 ((Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup V) V.subtype_injective).1 h)
  · exact Q.isPGroup'.map V.subtype
  · refine i1910a3_le_normalizer_of_forward fun x hx y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hy
    have h1 := Subgroup.smul_mem_pointwise_smul s (⟨x, hx⟩ : K) (Q : Subgroup V) hs
    rw [← Sylow.pointwise_smul_def, hQ] at h1
    exact ⟨_, h1, rfl⟩

theorem i1910a3_exists_lift_twoLocal
    {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (O : Subgroup M) [O.Normal] (hO : Nat.Coprime p (Nat.card O))
    (Pbar T : Subgroup (M ⧸ O))
    (hP : IsMulCommutative Pbar ∧ ∀ x ∈ Pbar, x ^ p = 1)
    (hT : T ≠ ⊥ ∧ IsPGroup 2 T)
    (hPT : Pbar ≤ Subgroup.normalizer (T : Set (M ⧸ O))) :
    ∃ P S : Subgroup M, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card Pbar ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      P ≤ Subgroup.normalizer (S : Set M) := by
  classical
  have hpf := Fact.mk hp
  set π : M →* M ⧸ O := QuotientGroup.mk' O with hπ
  have hker : ∀ x, π x = 1 ↔ x ∈ O := fun x => QuotientGroup.eq_one_iff x
  have hPbar : IsPGroup p Pbar := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hP.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPbar
  set Mhat : Subgroup M := Pbar.comap π with hMhat
  have hMhatcard : Nat.card Mhat = Nat.card O * p ^ n := by
    rw [hMhat, i1910a3_card_comap_mk, hn]
  let P0 : Sylow p Mhat := default
  have hP0card : Nat.card P0 = p ^ n := by
    rw [P0.card_eq_multiplicity, hMhatcard,
      Nat.factorization_mul Nat.card_pos.ne' (pow_pos hp.pos n).ne', Nat.factorization_pow]
    have h0 : (Nat.card O).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h => hp.one_lt.ne' (hO.eq_one_of_dvd h)
    simp [h0, hp.factorization_self]
  set Pm : Subgroup M := (P0 : Subgroup Mhat).map Mhat.subtype with hPm
  have hPmcard : Nat.card Pm = p ^ n := by
    rw [hPm, Subgroup.card_map_of_injective Mhat.subtype_injective]; exact hP0card
  have hPmp : IsPGroup p Pm := P0.isPGroup'.map Mhat.subtype
  have hPmle : Pm ≤ Mhat := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hPmπ : ∀ x ∈ Pm, π x ∈ Pbar := fun x hx => hPmle hx
  have hinj : ∀ x ∈ Pm, π x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ O := (hker x).1 h1
    obtain ⟨k, hk⟩ := hPmp ⟨x, hx⟩
    have hk' : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h3 : orderOf x ∣ Nat.card O := by
      have := Subgroup.orderOf_dvd_natCard O hxO
      exact this
    have h4 : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card O) := Nat.dvd_gcd h2 h3
    rw [(Nat.Coprime.pow_left k hO)] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have hcomm : ∀ x ∈ Pm, ∀ y ∈ Pm, x * y = y * x := by
    intro x hx y hy
    have hc : π x * π y = π y * π x :=
      congrArg Subtype.val (hP.1.is_comm.comm ⟨π x, hPmπ x hx⟩ ⟨π y, hPmπ y hy⟩)
    have := hinj (x * y * (y * x)⁻¹) (mul_mem (mul_mem hx hy) (inv_mem (mul_mem hy hx)))
      (by rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hexp : ∀ x ∈ Pm, x ^ p = 1 := fun x hx =>
    hinj (x ^ p) (pow_mem hx p) (by rw [map_pow]; exact hP.2 _ (hPmπ x hx))
  set V : Subgroup M := T.comap π with hV
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT.2
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hT.1 (Subgroup.card_eq_one.1 (by simpa using hm))
  have hVcard : Nat.card V = Nat.card O * 2 ^ m := by rw [hV, i1910a3_card_comap_mk, hm]
  have hnd : ¬ p ∣ Nat.card V := by
    intro h
    have hc : Nat.Coprime p (Nat.card V) := by
      rw [hVcard]
      exact Nat.Coprime.mul_right hO
        (Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
    exact hp.one_lt.ne' (hc.eq_one_of_dvd h)
  have hV2 : 2 ∣ Nat.card V := by
    rw [hVcard]; exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hPmN : Pm ≤ normalizer (V : Set M) := by
    refine i1910a3_le_normalizer_of_forward fun x hx y hy => ?_
    have hy' : π y ∈ T := hy
    show π (x * y * x⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hPT (hPmπ x hx)) (π y)).1 hy'
  obtain ⟨S, hS, hS2, hSN⟩ := i1910a3_exists_normalized_two_sylow hp hPmN hPmp hnd hV2
  exact ⟨Pm, S, ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp, hPmcard.trans hn.symm,
    hS, hS2, hSN⟩


end Lift

section Lower

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G] [Finite G]

theorem i1910a3_exists_twoLocal_lower {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G}
    (hBX : B ≤ X) (hB : IsElemAbelian p B) (hL : GLAPComponent p X L)
    (hZ : ∀ x : barOf p L, (∀ y, x * y = y * x) → x = 1)
    (E' T' : Subgroup (barOf p L)) (q : ℕ)
    (hE' : IsMulCommutative E' ∧ (∀ x ∈ E', x ^ p = 1) ∧ Nat.card E' = p ^ q)
    (hT' : T' ≠ ⊥ ∧ IsPGroup 2 T') (hET : E' ≤ Subgroup.normalizer (T' : Set (barOf p L))) :
    ∃ P S : Subgroup ↥X, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card (centB p B L) *
        p ^ (q * (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B) ∧
      S ≠ ⊥ ∧ IsPGroup 2 S ∧ P ≤ Subgroup.normalizer (S : Set ↥X) := by
  classical
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' _ with hπ
  set θ := barTheta p hL.1 hL.2.1 with hθ
  have hθinj := barTheta_injective p hL.1 hL.2.1
  let πB : ↥B →* ↥X ⧸ GLAPPrimeCore p ↥X := π.comp (Subgroup.inclusion hBX)
  have hBc : IsMulCommutative B := hB.1
  let I := ↥B ⧸ ((B ⊓ Subgroup.normalizer (L : Set G)).subgroupOf B)
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨r, hr⟩ : ∃ r : I → ↥B, ∀ i, (QuotientGroup.mk (r i) : I) = i :=
    ⟨fun i => (QuotientGroup.mk_surjective i).choose,
      fun i => (QuotientGroup.mk_surjective i).choose_spec⟩
  let ψ : I → (barOf p L →* ↥X ⧸ GLAPPrimeCore p ↥X) :=
    fun i => (MulAut.conj (πB (r i))⁻¹).toMonoidHom.comp θ
  have hψ : ∀ i, Function.Injective (ψ i) := fun i =>
    (MulAut.conj (πB (r i))⁻¹).injective.comp hθinj
  let Y : I → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := fun i => (ψ i).range
  let E : I → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := fun i => E'.map (ψ i)
  have hYbar : ∀ i, Y i = barX p X (GLBConj ((r i : ↥B) : G) L) := by
    intro i
    rw [barX_gLBConj p (hBX (r i).2) L, ← barTheta_range p hL.1 hL.2.1]
    exact MonoidHom.range_comp _ _
  have hcomp : ∀ i, GLAPComponent p X (GLBConj ((r i : ↥B) : G) L) := by
    intro i
    have h := glaPComponent_gLBConj hL ((r i : ↥B) : G)
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBX (r i).2))] at h
  have hYcomm : ∀ i j, i ≠ j → Y i ≤ Subgroup.centralizer (Y j : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i j hij
    have hne : barX p X (GLBConj ((r i : ↥B) : G) L) ≠ barX p X (GLBConj ((r j : ↥B) : G) L) := by
      intro h
      have h1 := glaPComponent_uniqueAux (hcomp i) (hcomp j) h
      have h2 := (gLBConj_eq_iff_mem_normalizer L _ _).1 h1
      apply hij
      rw [← hr i, ← hr j]
      apply QuotientGroup.eq.2
      rw [Subgroup.mem_subgroupOf]
      have h3 : (((r i)⁻¹ * r j : ↥B)) = r j * (r i)⁻¹ := hBc.is_comm.comm _ _
      rw [h3]
      exact ⟨((r j * (r i)⁻¹ : ↥B)).2, h2⟩
    have this : ⁅barX p X (GLBConj ((r i : ↥B) : G) L), barX p X (GLBConj ((r j : ↥B) : G) L)⁆ =
        ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp i).2.2.1
        (hcomp j).2.2.1 hne
    rw [← hYbar i, ← hYbar j] at this
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
  have hEY : ∀ i, E i ≤ Y i := fun i => Subgroup.map_le_range (ψ i) E'
  have hYz : ∀ i, ∀ y ∈ Y i, (∀ y' ∈ Y i, y * y' = y' * y) → y = 1 := by
    intro i y hy hc
    obtain ⟨x, rfl⟩ := hy
    have : x = 1 := hZ x fun z => hψ i (by
      rw [map_mul, map_mul]
      exact hc (ψ i z) ⟨z, rfl⟩)
    rw [this, map_one]
  let C0 : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := (c0Hom p B L hBX).range
  have hC0Y : ∀ i, C0 ≤ Subgroup.centralizer (Y i : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
    have hcX : ((c : ↥(centB p B L)) : G) ∈ X := hBX (centB_le p B L c.2)
    have h1 := centB_comm_theta (X := X) hL c.2 hcX ℓ
    have h2 : Commute (c0Hom p B L hBX c) (πB (r i)) := by
      show π _ * π _ = π _ * π _
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (c : G) * ((r i : ↥B) : G) = ((r i : ↥B) : G) * (c : G)
      exact congrArg Subtype.val (hBc.is_comm.comm (⟨(c : G), centB_le p B L c.2⟩ : ↥B) (r i))
    have h3 : Commute (c0Hom p B L hBX c) (θ (QuotientGroup.mk ℓ)) := h1
    have h4 : Commute (c0Hom p B L hBX c) (ψ i (QuotientGroup.mk ℓ)) := by
      show Commute _ ((πB (r i))⁻¹ * θ (QuotientGroup.mk ℓ) * (πB (r i))⁻¹⁻¹)
      exact (h2.inv_right.mul_right h3).mul_right h2.inv_right.inv_right
    exact h4.symm.eq
  have hCc : IsMulCommutative ↥(centB p B L) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hBc.is_comm.comm (⟨(a : G), centB_le p B L a.2⟩ : ↥B)
      ⟨(b : G), centB_le p B L b.2⟩
    have h2 : (a : G) * (b : G) = (b : G) * (a : G) := by
      have := congrArg Subtype.val this
      simpa using this
    exact Subtype.ext h2
  have hC : IsMulCommutative C0 ∧ ∀ x ∈ C0, x ^ p = 1 := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : ↥X ⧸ GLAPPrimeCore p ↥X) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, hCc.is_comm.comm x y]
    · rintro _ ⟨c, rfl⟩
      rw [← map_pow]
      have : c ^ p = 1 := Subtype.ext (hB.2 _ (centB_le p B L c.2))
      rw [this, map_one]
  have hCcard : Nat.card C0 = Nat.card (centB p B L) :=
    (Nat.card_congr (MonoidHom.ofInjective (c0Hom_injective L hBX hB)).toEquiv).symm
  have hE : ∀ i, IsMulCommutative (E i) ∧ (∀ x ∈ E i, x ^ p = 1) ∧ Nat.card (E i) = p ^ q := by
    intro i
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      show (a : ↥X ⧸ GLAPPrimeCore p ↥X) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE'.1.is_comm.comm (⟨x, hx⟩ : E') ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE'.2.1 x hx, map_one]
    · rw [Subgroup.card_map_of_injective (hψ i)]
      exact hE'.2.2
  obtain ⟨Pbar, hPc, hPe, hPcard, hPT⟩ := i1910a3_exists_elemAbelian_join hp Y E C0 q hYcomm hEY hYz hC0Y hC hE
  have hI : Nonempty I := ⟨1⟩
  obtain ⟨i0⟩ := hI
  let Tbar : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := T'.map (ψ i0)
  have hTY : Tbar ≤ Y i0 := Subgroup.map_le_range (ψ i0) T'
  have hTbar : Tbar ≠ ⊥ := fun h => hT'.1 ((Subgroup.map_eq_bot_iff_of_injective T' (hψ i0)).1 h)
  have hTbar2 : IsPGroup 2 Tbar := hT'.2.map (ψ i0)
  have hCT : C0 ≤ Subgroup.normalizer (Tbar : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTY (hC0Y i0 hx))
  have hET' : ∀ i, E i ≤ Subgroup.normalizer (Tbar : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.le_normalizer_map (ψ i) ⟨x, hET hx, rfl⟩
    · exact fun x hx => Subgroup.centralizer_le_normalizer _
        ((Subgroup.centralizer_le hTY).trans' (hEY i |>.trans (hYcomm i i0 hi)) hx)
  have hPcent := hPT Tbar hCT hET'
  obtain ⟨P, S, hPc', hPe', hPcard', hS, hS2, hPS⟩ := i1910a3_exists_lift_twoLocal hp hp2
    (GLAPPrimeCore p ↥X) (coprime_card_gLAPPrimeCore_aux p ↥X) Pbar Tbar ⟨hPc, hPe⟩
    ⟨hTbar, hTbar2⟩ hPcent
  refine ⟨P, S, hPc', hPe', ?_, hS, hS2, hPS⟩
  have hidx : Fintype.card I = (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B := by
    rw [← Nat.card_eq_fintype_card, Subgroup.relIndex, Subgroup.index_eq_card]
  rw [hPcard', hPcard, hCcard, hidx]


end Lower

end CFSG.HardMathSupport.Solomon.Coordinator
