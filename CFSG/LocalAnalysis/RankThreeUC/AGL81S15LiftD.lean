module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

open scoped MatrixGroups in
theorem not_k63List_three_aux_psl23_solvable : Group.IsSolvable PSL(2, ZMod 3) := by
  have h1 : Group.IsSolvable SL(2, ZMod 3) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
      (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (by decide)
  exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ZMod 3)))

theorem not_k63List_three (hList : KListI1) {S : Type} [Group S] [Finite S] (hI1 : ShapeI1 S)
    (hS : IsSimpleGroup S) (hnab : ¬ IsMulCommutative S) : ¬ K63List 3 S := by
  intro h
  unfold K63List at h
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, -⟩ | ⟨h7, -⟩
  · haveI := hS
    haveI := not_k63List_three_aux_psl23_solvable
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact hnab ⟨⟨fun a b => IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b⟩⟩
  · exact (hList S hI1).1 ⟨e⟩
  · exact shapeI1_not_alt5 hI1 ⟨e⟩
  · omega
  · omega

theorem k63_apply_aux_k63List_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {r : ℕ}
    (h : K63List r A) : K63List r B := by
  unfold K63List at h ⊢
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨hr, ⟨f⟩⟩ | ⟨hr, ⟨f⟩⟩ | ⟨hr, ⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, ⟨e.symm.trans f⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, ⟨e.symm.trans f⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, ⟨e.symm.trans f⟩⟩)))

theorem k63_apply_aux_pElement_normal {Y : Type} [Group Y] (p : ℕ) :
    (pElementSubgroup p (⊤ : Subgroup Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold pElementSubgroup at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top _, ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    refine ⟨k, ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [MulAut.conj_apply, hk] using this
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem k63_apply_aux_rElement {r : ℕ} (hr : r.Prime) {X S : Type} [Group X] [Finite X] [Group S]
    [Finite S] (h : X →* S) (hh : Function.Surjective h) (hrS : r ∣ Nat.card S) :
    ∃ x : X, (∃ k : ℕ, orderOf x = r ^ k) ∧ h x ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' r hrS
  obtain ⟨y, rfl⟩ := hh s
  have hdvd : r ∣ orderOf y := hs ▸ orderOf_map_dvd h y
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy0 r hr.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero r)
  refine ⟨y ^ m, ⟨a, ?_⟩, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 (by rw [hn]; exact dvd_mul_left m _), hn]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  · rw [map_pow]
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hs] at h2
    exact hm h2

theorem k63_apply_aux_pPrimeCore_le_centralizer {r : ℕ} (hr : r.Prime) {G : Type} [Group G]
    [Finite G] (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup r Q) :
    CFSG.pPrimeCore r G ≤ Subgroup.centralizer (Q : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI hK₀n : (CFSG.pPrimeCore r G).Normal := CFSG.pPrimeCore_normal
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hxQ : q * k * q⁻¹ * k⁻¹ ∈ Q := by
    have h1 : k * q⁻¹ * k⁻¹ ∈ Q := by simpa using ‹Q.Normal›.conj_mem q⁻¹ (Q.inv_mem hq) k
    have := Q.mul_mem hq h1
    simpa [mul_assoc] using this
  have hxK : q * k * q⁻¹ * k⁻¹ ∈ CFSG.pPrimeCore r G := by
    have h1 : q * k * q⁻¹ ∈ CFSG.pPrimeCore r G := by simpa using hK₀n.conj_mem k hk q
    exact (CFSG.pPrimeCore r G).mul_mem h1 ((CFSG.pPrimeCore r G).inv_mem hk)
  have hcop : Nat.Coprime r (Nat.card (CFSG.pPrimeCore r G)) := CFSG.pPrimeCore_coprime_card
  have hx1 : q * k * q⁻¹ * k⁻¹ = 1 := by
    obtain ⟨n, hn⟩ := hQ ⟨_, hxQ⟩
    have h1 : orderOf (q * k * q⁻¹ * k⁻¹) ∣ r ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hn
    have h2 : orderOf (q * k * q⁻¹ * k⁻¹) ∣ Nat.card (CFSG.pPrimeCore r G) :=
      Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore r G) hxK
    have h3 : Nat.Coprime (r ^ n) (Nat.card (CFSG.pPrimeCore r G)) := Nat.Coprime.pow_left n hcop
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  calc q * k = q * k * q⁻¹ * k⁻¹ * (k * q) := by group
    _ = k * q := by rw [hx1, one_mul]

theorem k63_apply_aux_solvable_normal_eq_bot {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ¬ IsMulCommutative S) (B : Subgroup S) [B.Normal] [Group.IsSolvable ↥B] : B = ⊥ := by
  haveI := hS
  rcases (inferInstance : B.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    haveI : Group.IsSolvable ↥(⊤ : Subgroup S) := by rw [← h]; infer_instance
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup S).subtype) (fun s => ⟨⟨s, trivial⟩, rfl⟩)
    exact hnab ⟨⟨fun a b => IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b⟩⟩

theorem k63_apply_core (hK63 : K63) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r = 3) {G : Type}
    [Group G] [Finite G] (hG : CFSG.Open.IsKGroup G) (hrk : CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 3)
    (Q V : Subgroup G) [Q.Normal] (hQ : IsPGroup r Q) (hQV : Q ⊔ V = ⊤)
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (Q : Set G))) {S : Type} [Group S]
    (f : ↥V →* S) (hf : Function.Surjective f) (hS : IsSimpleGroup S)
    (hnab : ¬ IsMulCommutative S) (hrS : r ∣ Nat.card S) : K63List r S := by
  subst hr3
  haveI : Fact (Nat.Prime 3) := ⟨hr⟩
  haveI : Finite S := Finite.of_surjective f hf
  set K₀ : Subgroup G := CFSG.pPrimeCore 3 G with hK₀
  haveI hK₀n : K₀.Normal := CFSG.pPrimeCore_normal
  let π : G →* G ⧸ K₀ := QuotientGroup.mk' K₀
  set P : Subgroup (G ⧸ K₀) := CFSG.pCore 3 (G ⧸ K₀) with hP
  haveI hPn : P.Normal := CFSG.pCore_normal
  let φ : G →* (G ⧸ K₀) ⧸ P := (QuotientGroup.mk' P).comp π
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective P).comp (QuotientGroup.mk'_surjective K₀)
  have hX : CFSG.Open.IsKGroup (G ⧸ K₀) := hG.quotient K₀
  have hcons := constrained_quotient hr Q hQ hC
  have hQP : Q.map π ≤ P :=
    le_sSup ⟨Subgroup.Normal.map ‹Q.Normal› π (QuotientGroup.mk'_surjective _), hQ.map π⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ K₀)) ≤ 3 := by
    have hker : ¬ 3 ∣ Nat.card π.ker := by
      rw [QuotientGroup.ker_mk']
      exact (Nat.Prime.coprime_iff_not_dvd hr).1 CFSG.pPrimeCore_coprime_card
    have hbar := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hr π hker ⊤
    rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      at hbar
    exact hbar.trans hrk
  let g : ↥V →* (G ⧸ K₀) ⧸ P := φ.comp V.subtype
  have hφQ : ∀ q ∈ Q, φ q = 1 := by
    intro q hq
    exact (QuotientGroup.eq_one_iff _).2 (hQP ⟨q, hq, rfl⟩)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    have hx : x ∈ Q ⊔ V := by rw [hQV]; trivial
    obtain ⟨q, hq, v, hv, hqv⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨⟨v, hv⟩, ?_⟩
    change φ v = φ x
    rw [← hqv, map_mul, hφQ q hq, one_mul]
  set K₁ : Subgroup G := P.comap π with hK₁
  have hK₁solv : Group.IsSolvable ↥K₁ := by
    have hK₀le : K₀ ≤ K₁ := by
      intro k hk
      show π k ∈ P
      have : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [this]
      exact P.one_mem
    have hK₀C : K₀ ≤ Subgroup.centralizer (Q : Set G) :=
      k63_apply_aux_pPrimeCore_le_centralizer hr Q hQ
    haveI : Group.IsSolvable ↥K₀ :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hK₀C)
        (Subgroup.inclusion_injective hK₀C)
    haveI : Group.IsSolvable ↥P := by
      haveI := (CFSG.pCore_isPGroup (p := 3) (G := G ⧸ K₀)).isNilpotent
      infer_instance
    let f₁ : ↥K₀ →* ↥K₁ := Subgroup.inclusion hK₀le
    let g₁ : ↥K₁ →* ↥P := (π.comp K₁.subtype).codRestrict P (fun k => k.2)
    refine solvable_of_ker_le_range f₁ g₁ ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : π x.1 = 1 := congrArg Subtype.val hx
    exact ⟨⟨x.1, (QuotientGroup.eq_one_iff _).1 h1⟩, rfl⟩
  have hker : g.ker ≤ f.ker := by
    set A : Subgroup ↥V := g.ker with hA
    haveI : A.Normal := MonoidHom.normal_ker g
    haveI : (A.map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hmemK₁ : ∀ a : ↥A, ((a : ↥V) : G) ∈ K₁ := by
      intro a
      have h1 : g (a : ↥V) = 1 := a.2
      have h2 : (QuotientGroup.mk' P) (π ((a : ↥V) : G)) = 1 := h1
      exact (QuotientGroup.eq_one_iff (π ((a : ↥V) : G))).1 h2
    let j : ↥A →* ↥K₁ := ((V.subtype).comp A.subtype).codRestrict K₁ hmemK₁
    have hj : Function.Injective j := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥K₁ => (x : G)) hab
    haveI := hK₁solv
    haveI hAs : Group.IsSolvable ↥A := solvable_of_solvable_injective hj
    haveI : Group.IsSolvable ↥(A.map f) :=
      solvable_of_surjective (MonoidHom.subgroupMap_surjective f A)
    exact (Subgroup.map_eq_bot_iff _).1 (k63_apply_aux_solvable_normal_eq_bot hS hnab _)
  let h : (G ⧸ K₀) ⧸ P →* S := (g.liftOfSurjective hg) ⟨f, hker⟩
  have hh : ∀ v : ↥V, h (g v) = f v := fun v =>
    g.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hg) ⟨f, hker⟩ v
  have hhs : Function.Surjective h := by
    intro s
    obtain ⟨v, rfl⟩ := hf s
    exact ⟨g v, hh v⟩
  let H : Subgroup ((G ⧸ K₀) ⧸ P) := pElementSubgroup 3 (⊤ : Subgroup ((G ⧸ K₀) ⧸ P))
  haveI hHn : H.Normal := k63_apply_aux_pElement_normal 3
  let h' : ↥H →* S := h.comp H.subtype
  have hh' : Function.Surjective h' := by
    obtain ⟨x, hxr, hx1⟩ := k63_apply_aux_rElement hr h hhs hrS
    have hxH : x ∈ H := Subgroup.subset_closure ⟨Subgroup.mem_top _, hxr⟩
    haveI : (H.map h).Normal := Subgroup.Normal.map hHn h hhs
    haveI := hS
    rcases (inferInstance : (H.map h).Normal).eq_bot_or_eq_top with h0 | h0
    · exfalso
      have hmem : h x ∈ H.map h := Subgroup.mem_map_of_mem h hxH
      rw [h0] at hmem
      exact hx1 (Subgroup.mem_bot.1 hmem)
    · intro s
      have hmem : s ∈ H.map h := by rw [h0]; trivial
      obtain ⟨y, hy, rfl⟩ := hmem
      exact ⟨⟨y, hy⟩, rfl⟩
  let N₁ : Subgroup ((G ⧸ K₀) ⧸ P) := H ⊓ h.ker
  have hN₁H : N₁ ≤ H := inf_le_left
  have hker' : N₁.subgroupOf H = h'.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  haveI hN₁n : (N₁.subgroupOf H).Normal := by
    rw [hker']
    exact MonoidHom.normal_ker h'
  let eH : (↥H ⧸ N₁.subgroupOf H) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective h' hh')
  have hS' : IsSimpleGroup (↥H ⧸ N₁.subgroupOf H) := by
    haveI := hS
    exact eH.isSimpleGroup
  have hnab' : ¬ IsMulCommutative (↥H ⧸ N₁.subgroupOf H) := by
    intro hc
    apply hnab
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, rfl⟩ := eH.surjective a
    obtain ⟨y, rfl⟩ := eH.surjective b
    rw [← map_mul, ← map_mul, hc.is_comm.comm x y]
  have hmain := hK63 (G ⧸ K₀) hX hcons hrank H N₁
    (CFSG.Open.IsSubnormal.refl _) hN₁H hN₁n hS' hnab'
  refine k63_apply_aux_k63List_of_equiv eH ?_
  rcases hmain with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, h⟩))

theorem k63_apply_amb (hK63 : K63) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r = 3) {Y : Type}
    [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y) (hrk : CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 3)
    (Q V : Subgroup Y) [Q.Normal] (hQ : IsPGroup r Q)
    (hC : Group.IsSolvable ↥((Q ⊔ V) ⊓ Subgroup.centralizer (Q : Set Y)))
    (N : Subgroup Y) (hNV : N ≤ V) [(N.subgroupOf V).Normal]
    (hS : IsSimpleGroup (↥V ⧸ N.subgroupOf V)) (hnab : ¬ IsMulCommutative (↥V ⧸ N.subgroupOf V))
    (hrS : r ∣ Nat.card (↥V ⧸ N.subgroupOf V)) : K63List r (↥V ⧸ N.subgroupOf V) := by
  set W : Subgroup Y := Q ⊔ V with hW
  have hQW : Q ≤ W := le_sup_left
  have hVW : V ≤ W := le_sup_right
  haveI hQn : (Q.subgroupOf W).Normal := ‹Q.Normal›.subgroupOf W
  have hKW : CFSG.Open.IsKGroup ↥W := hY.subgroup W
  have hrkW : CFSG.Open.pRank r (⊤ : Subgroup ↥W) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) W]
    exact (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans hrk
  have hQpg : IsPGroup r ↥(Q.subgroupOf W) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQW).symm
  have hsup : Q.subgroupOf W ⊔ V.subgroupOf W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQW hVW]
    exact Subgroup.subgroupOf_self W
  have hC' : Group.IsSolvable
      ↥(Subgroup.centralizer ((Q.subgroupOf W : Subgroup ↥W) : Set ↥W)) := by
    have hcm : ∀ c : ↥(Subgroup.centralizer ((Q.subgroupOf W : Subgroup ↥W) : Set ↥W)),
        ((c : ↥W) : Y) ∈ Subgroup.centralizer (Q : Set Y) := by
      intro c
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := (Subgroup.mem_centralizer_iff.1 c.2) (⟨q, hQW hq⟩ : ↥W) hq
      exact congrArg Subtype.val h1
    let j : ↥(Subgroup.centralizer ((Q.subgroupOf W : Subgroup ↥W) : Set ↥W)) →*
        ↥(W ⊓ Subgroup.centralizer (Q : Set Y)) :=
      ((W.subtype).comp
        (Subgroup.centralizer ((Q.subgroupOf W : Subgroup ↥W) : Set ↥W)).subtype).codRestrict
        (W ⊓ Subgroup.centralizer (Q : Set Y)) (fun c => ⟨c.1.2, hcm c⟩)
    have hj : Function.Injective j := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥(W ⊓ Subgroup.centralizer (Q : Set Y)) => (x : Y)) hab
    haveI := hC
    exact solvable_of_solvable_injective hj
  let e : ↥(V.subgroupOf W) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVW
  exact k63_apply_core hK63 hr hr2 hr3 hKW hrkW (Q.subgroupOf W) (V.subgroupOf W) hQpg hsup hC'
    ((QuotientGroup.mk' (N.subgroupOf V)).comp e.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.surjective) hS hnab hrS

end CFSG.LocalAnalysis.RankThreeUC.S15
