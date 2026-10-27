module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411Cover

public section

namespace CFSG.QuasithinUnique.Ch1

open scoped IsMulCommutative

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.Blueprint
open CFSG.Open (IsElemAbelian)

section Halving

theorem exists_halving_subgroup {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    (hN : N ≤ Subgroup.center K) (hsq : ∀ k ∈ N, k * k = 1) (hcard : 2 < Nat.card N) {κ : K}
    (hκ : κ ∈ N) :
    ∃ (H : Subgroup K) (n : K), H ≤ N ∧ κ ∈ H ∧ n ∈ N ∧ n ∉ H ∧
      ∀ k ∈ N, k ∈ H ∨ n * k ∈ H := by
  classical
  have hcomm : ∀ a ∈ N, ∀ b : K, a * b = b * a := fun a ha b =>
    (Subgroup.mem_center_iff.1 (hN ha) b).symm
  let S : Set (Subgroup K) := {H | H ≤ N ∧ κ ∈ H ∧ H ≠ N}
  have hSne : S.Nonempty := by
    refine ⟨Subgroup.zpowers κ, ?_, Subgroup.mem_zpowers κ, ?_⟩
    · rw [Subgroup.zpowers_le]
      exact hκ
    · intro h
      have h1 : Nat.card (Subgroup.zpowers κ) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq κ hκ))
      rw [h] at h1
      omega
  obtain ⟨H, ⟨hHN, hκH, hHne⟩, hmax⟩ := (Set.toFinite S).exists_maximal hSne
  obtain ⟨n, hnN, hnH⟩ : ∃ n ∈ N, n ∉ H := by
    by_contra hcon
    exact hHne (le_antisymm hHN fun x hx => by_contra fun hxH => hcon ⟨x, hx, hxH⟩)
  have hnn : n * n = 1 := hsq n hnN
  have hnc : ∀ y : K, n * y = y * n := hcomm n hnN
  let H' : Subgroup K :=
    { carrier := {x | x ∈ H ∨ n * x ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · refine Or.inr ?_
          have : n * (x * y) = x * (n * y) := by
            calc n * (x * y) = (n * x) * y := (mul_assoc _ _ _).symm
              _ = (x * n) * y := by rw [hnc x]
              _ = x * (n * y) := mul_assoc _ _ _
          rw [this]
          exact H.mul_mem hx hy
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (n * x) * (n * y) := by
            calc x * y = (n * n) * x * y := by rw [hnn, one_mul]
              _ = n * (n * x) * y := by rw [mul_assoc n n x]
              _ = n * (x * n) * y := by rw [hnc x]
              _ = (n * x) * (n * y) := by simp only [mul_assoc]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ?_
          have h1 : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
          have : n * x⁻¹ = (n * x)⁻¹ := by
            rw [mul_inv_rev, h1, hnc x⁻¹]
          rw [this]
          exact H.inv_mem hx }
  have hH'N : H' ≤ N := by
    intro x hx
    rcases hx with hx | hx
    · exact hHN hx
    · have h1 : n⁻¹ * (n * x) ∈ N := N.mul_mem (N.inv_mem hnN) (hHN hx)
      rwa [inv_mul_cancel_left] at h1
  have hHH' : H ≤ H' := fun x hx => Or.inl hx
  by_cases hEq : H' = N
  · refine ⟨H, n, hHN, hκH, hnN, hnH, fun k hk => ?_⟩
    have : k ∈ H' := hEq ▸ hk
    exact this
  · exfalso
    have hH'S : H' ∈ S := ⟨hH'N, hHH' hκH, hEq⟩
    have hle : H' ≤ H := hmax hH'S hHH'
    have hnH' : n ∈ H' := Or.inr (by rw [hnn]; exact H.one_mem)
    exact hnH (hle hnH')

end Halving

section Quotient

theorem exists_quotExt {K : Type*} [Group K] (φ : K →* Equiv.Perm (Fin 22)) (H : Subgroup K)
    [H.Normal] (n : K) (hHφ : ∀ h ∈ H, φ h = 1) (hnφ : φ n = 1) (hnH : n ∉ H)
    (hnn : n * n ∈ H) (hnc : ∀ k, n * k = k * n)
    (hker : ∀ k, φ k = 1 → k ∈ H ∨ n * k ∈ H) :
    ∃ X : CentralExt (K ⧸ H) (Equiv.Perm (Fin 22)), ∀ k : K, X.φ (k : K ⧸ H) = φ k := by
  refine ⟨⟨QuotientGroup.lift H φ (fun h hh => hHφ h hh), (n : K ⧸ H), ?_, ?_, ?_, ?_, ?_⟩,
    fun k => rfl⟩
  · exact hnφ
  · intro h
    exact hnH ((QuotientGroup.eq_one_iff n).1 h)
  · rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 hnn
  · intro e
    induction e using QuotientGroup.induction_on with
    | _ k => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hnc k]
  · intro e he
    induction e using QuotientGroup.induction_on with
    | _ k =>
      have hk : φ k = 1 := he
      rcases hker k hk with h | h
      · exact Or.inl ((QuotientGroup.eq_one_iff k).2 h)
      · refine Or.inr ?_
        have h1 : (n : K ⧸ H) * (k : K ⧸ H) = 1 := by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq_one_iff _).2 h
        have h2 : (n : K ⧸ H) * (n : K ⧸ H) = 1 := by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq_one_iff _).2 hnn
        exact mul_left_cancel (h1.trans h2.symm)

end Quotient

section Gaschuetz

theorem false_of_double_cover
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (X : CentralExt E (Equiv.Perm (Fin 22)))
    (hrange : ∀ y ∈ NativeSporadic.M22, ∃ e : E, X.φ e = y)
    (hφmem : ∀ e, X.φ e ∈ NativeSporadic.M22) (xt : Fin 3 → E)
    (hxt : ∀ i, X.φ (xt i) = covData.x i)
    (hfree : ∀ e ∈ covData.free, cE covData.tab xt e = 0) : False := by
  classical
  have hxmem : ∀ i, covData.x i ∈ NativeSporadic.M22 := fun i => wordP_mem _
  have hlift : ∀ bl ∈ covData.blocks, ∃ gt : E, X.φ gt = bl.g := fun bl _ =>
    hrange _ bl.g_mem
  have hT := covCheck_good covCheck_covData
  have hzero := covCheck_vanish covData covCheck_covData X xt hxt hlift hfree
  obtain ⟨s, hs⟩ := exists_section X xt hT hxt hzero
  let Sg := covData.tab.sub covData.x hT
  have hSgD : Sg ≤ NativeSporadic.M22 := by
    rintro g ⟨v, -, rfl⟩
    exact Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact hxmem i
  have hcardSg : Nat.card Sg = 128 := by
    rw [CayTab.card_sub hT]
    exact covData_nV
  have hidx : (Sg.subgroupOf NativeSporadic.M22).index = 3465 := by
    have h1 := Subgroup.card_mul_index (Sg.subgroupOf NativeSporadic.M22)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSgD).toEquiv, hcardSg,
      CFSG.Sporadic.Mathieu.card_M22] at h1
    omega
  let V : Subgroup E := X.φ.ker
  let P : Subgroup E := Sg.comap X.φ
  let K : Subgroup E := s.range
  have hVφ : ∀ v ∈ V, X.φ v = 1 := fun v hv => hv
  have hζV : X.ζ ∈ V := X.φ_ζ
  have hVcard : Nat.card V = 2 := by
    rw [Nat.card_eq_two_iff' (1 : V)]
    refine ⟨⟨X.ζ, hζV⟩, ?_, ?_⟩
    · intro h
      exact X.ne_one (congrArg Subtype.val h)
    · intro y hy
      rcases X.ker y.1 y.2 with h | h
      · exact absurd (Subtype.ext h) hy
      · exact Subtype.ext h
  have hrangeφ : X.φ.range = NativeSporadic.M22 := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact hφmem e
    · intro hy
      exact hrange y hy
  have hPidx : P.index = 3465 := by
    rw [Subgroup.index_comap, hrangeφ]
    exact hidx
  have hVP : V ≤ P := fun v hv => by
    show X.φ v ∈ Sg
    rw [hVφ v hv]
    exact Sg.one_mem
  have hKP : K ≤ P := by
    rintro _ ⟨g, rfl⟩
    show X.φ (s g) ∈ Sg
    rw [hs g]
    exact g.2
  have hVcentral : ∀ v ∈ V, ∀ e : E, v * e = e * v := by
    intro v hv e
    rcases X.ker v hv with rfl | rfl
    · simp
    · exact X.central e
  have hVK : V ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, g, rfl⟩
    have h1 : g = 1 := by
      apply Subtype.ext
      have := hVφ _ hyV
      rw [hs g] at this
      exact this
    rw [h1, map_one]
    exact Subgroup.one_mem _
  have hVKP : V ⊔ K = P := by
    apply le_antisymm (sup_le hVP hKP)
    intro p hp
    have hpS : X.φ p ∈ Sg := hp
    have hmem : p * (s ⟨X.φ p, hpS⟩)⁻¹ ∈ V := by
      show X.φ _ = 1
      rw [map_mul, map_inv, hs ⟨X.φ p, hpS⟩]
      simp
    have hK' : s (⟨X.φ p, hpS⟩ : Sg) ∈ K := ⟨_, rfl⟩
    have := Subgroup.mul_mem_sup hmem hK'
    simpa using this
  have hVn : V.Normal := inferInstanceAs X.φ.ker.Normal
  have hVcomm : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hVcentral a a.2 b)⟩⟩
  have hcop : Nat.Coprime P.index (Nat.card V) := by
    rw [hPidx, hVcard]
    decide
  obtain ⟨D', -, hVD, hsupD⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting V P K hcop hVK hVKP
  have hDn : D'.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hg : g ∈ V ⊔ D' := by rw [hsupD]; trivial
    obtain ⟨v, hv, d₀, hd₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    have h1 : v * d₀ * d * (v * d₀)⁻¹ = v * (d₀ * d * d₀⁻¹) * v⁻¹ := by group
    have h2 : v * (d₀ * d * d₀⁻¹) * v⁻¹ = d₀ * d * d₀⁻¹ := by
      rw [hVcentral v hv, mul_inv_cancel_right]
    rw [h1, h2]
    exact D'.mul_mem (D'.mul_mem hd₀ hd) (D'.inv_mem hd₀)
  have hcomm' : ∀ a b : E ⧸ D', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
        have ha : a ∈ V ⊔ D' := by rw [hsupD]; trivial
        have hb : b ∈ V ⊔ D' := by rw [hsupD]; trivial
        obtain ⟨v₁, hv₁, d₁, hd₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
        obtain ⟨v₂, hv₂, d₂, hd₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hb
        have e1 : ((v₁ * d₁ : E) : E ⧸ D') = (v₁ : E ⧸ D') := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d₁).2 hd₁, mul_one]
        have e2 : ((v₂ * d₂ : E) : E ⧸ D') = (v₂ : E ⧸ D') := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d₂).2 hd₂, mul_one]
        rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hVcentral v₁ hv₁ v₂]
  have : IsMulCommutative (E ⧸ D') := ⟨⟨hcomm'⟩⟩
  have hsub : Subsingleton (E ⧸ D') := inferInstance
  have hζD : X.ζ ∈ D' := (QuotientGroup.eq_one_iff _).1 (Subsingleton.elim _ _)
  have : X.ζ ∈ V ⊓ D' := ⟨hζV, hζD⟩
  rw [hVD] at this
  exact X.ne_one ((Subgroup.mem_bot).1 this)

end Gaschuetz

theorem m22CoverCyclic :
    Lin2.M22CoverCyclic := by
  classical
  intro K _ _ hK p₀ hp₀ hker₀ hel₀
  have : Group.IsPerfect K := hK
  by_contra hcon
  let p : K →* NativeSporadic.M22 := p₀
  have hp : Function.Surjective p := hp₀
  have hker : p.ker ≤ Subgroup.center K := hker₀
  have hel : IsElemAbelian 2 p.ker := hel₀
  have hcard : 2 < Nat.card p.ker := Nat.lt_of_not_le hcon
  let φ : K →* Equiv.Perm (Fin 22) := NativeSporadic.M22.subtype.comp p
  have hφ : ∀ k, φ k = ((p k : NativeSporadic.M22) : Equiv.Perm (Fin 22)) := fun k => rfl
  have hφ1 : ∀ k, φ k = 1 ↔ p k = 1 := by
    intro k
    rw [hφ]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hxmem : ∀ i, covData.x i ∈ NativeSporadic.M22 := fun i => wordP_mem _
  choose xt hxt using fun i : Fin 3 => hp ⟨covData.x i, hxmem i⟩
  have hxt' : ∀ i, φ (xt i) = covData.x i := fun i => by rw [hφ, hxt i]
  have hT := covCheck_good covCheck_covData
  have hnV : 189 / 3 < covData.tab.nV := by
    show 189 / 3 < covData.nV
    rw [covData_nV]
    norm_num
  let κ : K := kap covData.tab xt (189 / 3) (fo 189)
  have hκφ : φ κ = 1 := hom_kap xt hT hxt' hnV (fo 189)
  have hκN : κ ∈ p.ker := (MonoidHom.mem_ker).2 ((hφ1 κ).1 hκφ)
  have hsq : ∀ k ∈ p.ker, k * k = 1 := fun k hk => by
    rw [← pow_two]
    exact hel.2 k hk
  obtain ⟨H, n, hHN, hκH, hnN, hnH, hcover⟩ := exists_halving_subgroup hker hsq hcard hκN
  have : H.Normal := Subgroup.normal_of_le_center (hHN.trans hker)
  have hHφ : ∀ h ∈ H, φ h = 1 := fun h hh => (hφ1 h).2 (hHN hh)
  obtain ⟨X, hX⟩ := exists_quotExt φ H n hHφ ((hφ1 n).2 hnN) hnH
    (by rw [hsq n hnN]; exact H.one_mem) (fun k => (Subgroup.mem_center_iff.1 (hker hnN) k).symm)
    (fun k hk => hcover k ((hφ1 k).1 hk))
  have hX' : ∀ k : K, X.φ (QuotientGroup.mk' H k) = φ k := hX
  refine false_of_double_cover X ?_ ?_ (fun i => QuotientGroup.mk' H (xt i)) ?_ ?_
  · intro y hy
    obtain ⟨k, hk⟩ := hp ⟨y, hy⟩
    exact ⟨QuotientGroup.mk' H k, by rw [hX', hφ, hk]⟩
  · intro e
    induction e using QuotientGroup.induction_on with
    | _ k =>
      rw [hX k, hφ]
      exact (p k).2
  · intro i
    rw [hX']
    exact hxt' i
  · intro e he
    rw [covData_free] at he
    have he' : e = 189 := by simpa using he
    subst he'
    unfold cE
    have h1 := map_kap xt (QuotientGroup.mk' H) covData.tab (189 / 3) (fo 189)
    have h2 : kap covData.tab (fun i => QuotientGroup.mk' H (xt i)) (189 / 3) (fo 189) = 1 := by
      rw [← h1]
      exact (QuotientGroup.eq_one_iff _).2 hκH
    simp only [h2, ↓reduceIte]

end CFSG.QuasithinUnique.Ch1
