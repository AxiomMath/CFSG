module

public import CFSG.CGT.Stroth77.Section223Odd
public import CFSG.CGT.Stroth77.Section223Ext
public import CFSG.CGT.Stroth77.Section223ExtStep
public import CFSG.CGT.Stroth77.WeakTransport
public import CFSG.CGT.Stroth76.NoInvFrame

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace S223

theorem card_add_self_eq_zero_le_four {k : Fin 3 → ℕ} {i : Fin 3} (hi : k i = 0) :
    Nat.card {v : Torus k // v + v = 0} ≤ 4 := by
  have hcard : Nat.card ({j : Fin 3 // j ≠ i} → Bool) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]
    fin_cases i <;> rfl
  have hsub : ∀ (m : ℕ) (x y : ZMod (2 ^ m)), m = 0 → x = y := by
    rintro m x y rfl
    exact Subsingleton.elim (α := ZMod 1) x y
  let f : {v : Torus k // v + v = 0} → ({j : Fin 3 // j ≠ i} → Bool) :=
    fun v j => decide (v.1 j.1 ≠ 0)
  have hf : Function.Injective f := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    apply Subtype.ext
    funext j
    change v j = w j
    rcases eq_or_ne j i with rfl | hj
    · exact hsub _ _ _ hi
    · have hji := congrFun h ⟨j, hj⟩
      simp only [f, decide_eq_decide] at hji
      have hvj := zmod_two_pow_eq_zero_or_of_add_self (v j) (congrFun hv j)
      have hwj := zmod_two_pow_eq_zero_or_of_add_self (w j) (congrFun hw j)
      rcases hvj with h0 | h1 <;> rcases hwj with h0' | h1'
      · rw [h0, h0']
      · by_cases hz : w j = 0
        · rw [h0, hz]
        · exact absurd (hji.mpr hz) (not_not.mpr h0)
      · by_cases hz : v j = 0
        · rw [hz, h0']
        · exact absurd (hji.mp hz) (not_not.mpr h0')
      · rw [h1, h1']
  calc Nat.card {v : Torus k // v + v = 0} ≤ Nat.card ({j : Fin 3 // j ≠ i} → Bool) :=
        Nat.card_le_card_of_injective f hf
    _ = 4 := hcard

theorem mem_normalizer_of_le_commX {G : Type} [Group G] [Finite G] {D C V : Subgroup G}
    (hDC : D ≤ C) (hCX : C ≤ commX D V) {v : G} (hv : v ∈ V) :
    v ∈ Subgroup.normalizer (C : Set G) := by
  have h : v⁻¹ ∈ Subgroup.normalizer (C : Set G) := mem_normalizer_of_conj_mem fun x hx => by
    rw [inv_inv, show v⁻¹ * x * v = x * (x⁻¹ * (v⁻¹ * x * v)) by group]
    exact mul_mem hx (hDC ((hCX hx).2 v hv))
  have := inv_mem h
  rwa [inv_inv] at this

end S223

namespace StrothFrame

variable {G : Type} [Group G] [Finite G]

theorem isTyped_A (F : StrothFrame G) : F.IsTyped F.A F.dA :=
  ⟨le_rfl, F.A_le_S, rfl, rfl, rfl, rfl⟩

namespace IsTyped

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem one_le_k (h : F.IsTyped D dD) (i : Fin 3) : 1 ≤ τ.k i := by
  by_contra hi
  have h8 : Nat.card (omegaIn 1 D) = 8 := by rw [h.omegaIn_one_eq]; exact F.card_omegaIn_one_A
  have h4 := (card_omegaIn_one_eq dD.e).trans_le
    (S223.card_add_self_eq_zero_le_four (k := τ.k) (i := i) (by omega))
  omega

theorem exists_typed_card_lt_of_ne (hext : StrothExtStep) (h : F.IsTyped D dD)
    (hns : ¬ IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D)
    (hτ : τ ≠ StrothTypeIndex.t101 0) :
    ∃ (F' : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
      (dD' : StrothWeakTypeData D' τ'), F'.IsTyped D' dD' ∧ Nat.card D < Nat.card D' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, Q, hoE, hoD, hoodd, hρodd, hu, hQ, hDQ, hQX, huQ, hρQ, hρ3Q⟩ :=
    h.exists_rho_change hns
  have hQC : Q ≤ Subgroup.centralizer (D : Set G) := fun x hx => (hQX hx).1
  have hρD : F.dA.ρ * o ∈ Subgroup.normalizer (D : Set G) :=
    mul_mem h.ρ_mem_normalizer (Subgroup.centralizer_le_normalizer _ hoD)
  obtain ⟨C, hDC, hCQ, hcard, hsq, huC, hρC⟩ := S223.exists_ext_two_four hQ hDQ hQC
    h.u_mem_normalizer huQ hρD hρQ F.dA.u_sq hu hρ3Q
  have hCX : C ≤ S223.commX D F.V := hCQ.trans hQX
  have hCD : C ≤ Subgroup.centralizer (D : Set G) := hCQ.trans hQC
  have huvC : F.dA.uv ∈ Subgroup.normalizer (C : Set G) :=
    S223.mem_normalizer_of_le_commX hDC.le hCX F.uv_mem_V
  have htC : F.dA.t ∈ Subgroup.normalizer (C : Set G) :=
    S223.mem_normalizer_of_le_commX hDC.le hCX F.t_mem_V
  have hoA : o ∈ Subgroup.centralizer (F.A : Set G) := Subgroup.centralizer_le h.A_le hoD
  let F₁ := F.withRho hoA hoE hoodd hρodd hu
  let T : Subgroup G := Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u}
  have hTle : ∀ {H : Subgroup G}, F.dA.uv ∈ H → F.dA.t ∈ H → F.dA.u ∈ H → T ≤ H := by
    intro H h1 h2 h3
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [h1, h2, h3]
  have hTp : IsPGroup 2 T := F.S.2.to_le (hTle F.uv_mem_S F.t_mem_S F.u_mem_S)
  have hP : IsPGroup 2 (C ⊔ T : Subgroup G) :=
    (hQ.to_le hCQ).to_sup_of_normal_left' hTp (hTle huvC htC huC)
  have hPN : C ⊔ T ≤ Subgroup.normalizer (F₁.A : Set G) := sup_le
    (hCD.trans ((Subgroup.centralizer_le h.A_le).trans (Subgroup.centralizer_le_normalizer _)))
    (hTle F.dA.uv_mem F.dA.t_mem F.dA.u_mem)
  have hsubT : ∀ {x : G}, x ∈ ({F.dA.uv, F.dA.t, F.dA.u} : Set G) → x ∈ C ⊔ T := fun hx =>
    (le_sup_right : T ≤ C ⊔ T) (Subgroup.subset_closure hx)
  obtain ⟨S'', hA'', huv'', ht'', hu'', hns'', hPS''⟩ := F₁.exists_withSylow_of_le hP hPN
    (h.A_le.trans (hDC.le.trans le_sup_left)) (hsubT (x := F.dA.uv) (by simp))
    (hsubT (x := F.dA.t) (by simp)) (hsubT (x := F.dA.u) (by simp))
  let F₂ := F₁.withSylow S'' hA'' huv'' ht'' hu'' hns''
  have hCS : C ≤ (F₂.S : Subgroup G) := le_sup_left.trans hPS''
  have huvo : o * dD.uv = dD.uv * o := by
    rw [h.uv_eq]; exact F.comm_uv_of_mem_centralizer_E hoE
  have hto : o * dD.t = dD.t * o := by
    rw [h.t_eq]; exact F.comm_t_of_mem_centralizer_E hoE
  have hρodd' : Odd (orderOf (dD.ρ * o)) := by rw [h.ρ_eq]; exact hρodd
  have hu' : dD.u * (dD.ρ * o) * dD.u * (dD.ρ * o) = 1 := by rw [h.u_eq, h.ρ_eq]; exact hu
  let dD₁ := dD.mulRho o hoD huvo hto hρodd' hu'
  have hL : dD₁.L ≤ Subgroup.normalizer C := by
    rw [StrothWeakTypeData.L, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · show dD.uv ∈ Subgroup.normalizer (C : Set G)
      rw [h.uv_eq]; exact huvC
    · show dD.t ∈ Subgroup.normalizer (C : Set G)
      rw [h.t_eq]; exact htC
    · show dD.u ∈ Subgroup.normalizer (C : Set G)
      rw [h.u_eq]; exact huC
    · show dD.ρ * o ∈ Subgroup.normalizer (C : Set G)
      rw [h.ρ_eq]; exact hρC
  have hρ3 : dD₁.ρ ^ 3 ∈ Subgroup.centralizer (C : Set G) := by
    show (dD.ρ * o) ^ 3 ∈ Subgroup.centralizer (C : Set G)
    rw [h.ρ_eq]
    exact Subgroup.centralizer_le hCQ hρ3Q
  have : Finite (dD₁.AuxGroup hL) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hNI : NoInvolutionsCentralizing C D :=
    CFSG.CGT.Stroth76.frame_noInvolutionsCentralizing_of_conj F₂ h.A_le
      (fun b hb hb2 => h.mem_A_of_mul_self hb hb2) hCS hCD
      (fun z hz => (hCX hz).2 _ F.uv_mem_V) (fun z hz => (hCX hz).2 _ F.t_mem_V)
  obtain ⟨τ', D', huv', ht', hu₁, hρ'⟩ := hext (dD₁.toAux hL hDC.le hρ3) h.one_le_k hτ
    (dD₁.auxSub_mono hL hDC.le) (dD₁.auxSub_le_centralizer hL hCD)
    (by rw [dD₁.card_auxSub hL le_rfl, dD₁.card_auxSub hL hDC.le]; exact hcard)
    (fun x hx => by
      obtain ⟨n, hn, rfl⟩ := (dD₁.mem_auxSub hL).mp hx
      rw [← map_mul]
      exact (dD₁.inl_mem_auxSub hL).mpr (hsq n hn))
    (dD₁.toAux_L_le hL hDC.le hρ3)
    (dD₁.noInvolutionsCentralizing_auxSub hL hDC.le hNI le_rfl) le_rfl
  let dC := dD₁.ofAux hL le_rfl D' huv' ht' hu₁ hρ'
  refine ⟨F₂, C, τ', dC, ⟨h.A_le.trans hDC.le, hCS, h.uv_eq, h.t_eq, h.u_eq, ?_⟩,
    Subgroup.card_lt_of_lt hDC⟩
  show dD.ρ * o = F.dA.ρ * o
  rw [h.ρ_eq]

theorem exists_typed_card_lt (hext : StrothExtStep) (h : F.IsTyped D dD)
    (hns : ¬ IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) :
    ∃ (F' : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
      (dD' : StrothWeakTypeData D' τ'), F'.IsTyped D' dD' ∧ Nat.card D < Nat.card D' := by
  by_cases hτ : τ = StrothTypeIndex.t101 0
  · subst hτ
    have hcard : Nat.card D = Nat.card F.A := by
      rw [dD.card, F.card_A]
      rfl
    obtain rfl : F.A = D := Subgroup.eq_of_le_of_card_ge h.A_le hcard.le
    exact F.isTyped_A.exists_typed_card_lt_of_ne hext hns (by intro h; cases h)
  · exact h.exists_typed_card_lt_of_ne hext hns hτ

theorem exists_isD_isSylowIn_card_le (hext : StrothExtStep) (h : F.IsTyped D dD) :
    ∃ (F₁ : StrothFrame G) (D₁ : Subgroup G) (τ₁ : StrothTypeIndex)
      (dD₁ : StrothWeakTypeData D₁ τ₁), F₁.IsD D₁ dD₁ ∧
      IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
        ((F₁.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧
      Nat.card D ≤ Nat.card D₁ := by
  suffices key : ∀ n : ℕ, ∀ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex)
      (dD : StrothWeakTypeData D τ), F.IsTyped D dD → Nat.card G - Nat.card D = n →
      ∃ (F₁ : StrothFrame G) (D₁ : Subgroup G) (τ₁ : StrothTypeIndex)
        (dD₁ : StrothWeakTypeData D₁ τ₁), F₁.IsD D₁ dD₁ ∧
        IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
          ((F₁.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧
        Nat.card D ≤ Nat.card D₁ from key _ F D τ dD h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F D τ dD h hn
    by_cases hsyl : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D
    · obtain ⟨F', hF', hS'⟩ := h.exists_isSylowIn_normalizer hsyl
      exact ⟨F', D, τ, dD, hF', hS', le_rfl⟩
    · obtain ⟨F', D', τ', dD', h', hlt⟩ := h.exists_typed_card_lt hext hsyl
      have hle : Nat.card D' ≤ Nat.card G := Subgroup.card_le_card_group D'
      obtain ⟨F₁, D₁, τ₁, dD₁, h₁, h₂, h₃⟩ := ih _ (by omega) F' D' τ' dD' h' rfl
      exact ⟨F₁, D₁, τ₁, dD₁, h₁, h₂, hlt.le.trans h₃⟩

end IsTyped

end StrothFrame

theorem stroth_2_23_frame_of_strothExtStep (hext : StrothExtStep) :
    ∀ {G : Type} [Group G] [Finite G], StrothFrame G →
      ∃ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
        F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) := by
  intro G _ _ F
  obtain ⟨F₁, D₁, τ₁, dD₁, h₁, h₂, -⟩ := F.isTyped_A.exists_isD_isSylowIn_card_le hext
  exact ⟨F₁, D₁, τ₁, dD₁, h₁, h₂⟩

end CFSG.CGT.Stroth77
