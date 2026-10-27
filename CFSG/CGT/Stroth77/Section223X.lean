module

public import CFSG.CGT.Stroth77.Section223Step
public import CFSG.CGT.Stroth77.Section223XRho

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothFrame.IsTyped

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {X : Subgroup G}

theorem exists_typed_lt_le_of_ne (hext : StrothExtStep) (hXc : IsMulCommutative X)
    (hXS : X ≤ (F.S : Subgroup G)) (huvX : F.dA.uv ∈ Subgroup.normalizer (X : Set G))
    (htX : F.dA.t ∈ Subgroup.normalizer (X : Set G))
    (huX : F.dA.u ∈ Subgroup.normalizer (X : Set G))
    (hρX : F.dA.ρ ∈ Subgroup.normalizer (X : Set G))
    (hρ3X : F.dA.ρ ^ 3 ∈ Subgroup.centralizer (X : Set G))
    {B : Subgroup G} {τ : StrothTypeIndex} {dB : StrothWeakTypeData B τ}
    (h : F.IsTyped B dB) (hτ : τ ≠ StrothTypeIndex.t101 0) (hBX : B < X) :
    ∃ (C : Subgroup G) (τ' : StrothTypeIndex) (dC : StrothWeakTypeData C τ'),
      F.IsTyped C dC ∧ B < C ∧ C ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hXc.is_comm.comm (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have hXB : X ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hXcomm b (hBX.le hb) x hx
  have hXp : IsPGroup 2 X := F.S.2.to_le hXS
  have hVX : F.V ≤ Subgroup.normalizer (X : Set G) := by
    rw [StrothFrame.V, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact huvX
    · exact htX
  set Q := X ⊓ S223.commX B F.V with hQ
  have hP : IsPGroup 2 (X ⊔ F.V : Subgroup G) := hXp.to_sup_of_normal_left' F.isPGroup_V hVX
  obtain ⟨d, hdX, hdB, -, hdc⟩ := S223.exists_mem_sq_comm_mem hP hBX le_sup_left
    (sup_le (hXB.trans (Subgroup.centralizer_le_normalizer _)) h.V_le_normalizer)
    (sup_le Subgroup.le_normalizer hVX)
  have hBQ : B ≤ Q := le_inf hBX.le (S223.le_commX h.comm h.V_le_normalizer)
  have hdQ : d ∈ Q := ⟨hdX, hXB hdX, fun v hv => by
    have := hdc v (Subgroup.mem_sup_right hv)
    simpa [mul_assoc] using this⟩
  have hBQ' : B < Q := SetLike.lt_iff_le_and_exists.mpr ⟨hBQ, d, hdQ, hdB⟩
  have hQX : Q ≤ X := inf_le_left
  have hQC : Q ≤ Subgroup.centralizer (B : Set G) := hQX.trans hXB
  have huQ : F.dA.u ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inf_normalizer_le_normalizer_inf
    ⟨huX, S223.mem_normalizer_commX h.u_mem_normalizer F.u_mem_normalizer_V⟩
  have hρQ : F.dA.ρ ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hρX, S223.mem_normalizer_commX h.ρ_mem_normalizer F.ρ_mem_normalizer_V⟩
  obtain ⟨C, hBC, hCQ, hcard, hsq, huC, hρC⟩ := S223.exists_ext_two_four (hXp.to_le hQX) hBQ' hQC
    h.u_mem_normalizer huQ h.ρ_mem_normalizer hρQ F.dA.u_sq F.dA.u_rho
    (Subgroup.centralizer_le hQX hρ3X)
  have hCX : C ≤ X := hCQ.trans hQX
  have hCcX : C ≤ S223.commX B F.V := hCQ.trans inf_le_right
  have hCB : C ≤ Subgroup.centralizer (B : Set G) := hCQ.trans hQC
  have huvC : F.dA.uv ∈ Subgroup.normalizer (C : Set G) :=
    S223.mem_normalizer_of_le_commX hBC.le hCcX F.uv_mem_V
  have htC : F.dA.t ∈ Subgroup.normalizer (C : Set G) :=
    S223.mem_normalizer_of_le_commX hBC.le hCcX F.t_mem_V
  have hL : dB.L ≤ Subgroup.normalizer C := by
    rw [StrothWeakTypeData.L, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · show dB.uv ∈ Subgroup.normalizer (C : Set G)
      rw [h.uv_eq]; exact huvC
    · show dB.t ∈ Subgroup.normalizer (C : Set G)
      rw [h.t_eq]; exact htC
    · show dB.u ∈ Subgroup.normalizer (C : Set G)
      rw [h.u_eq]; exact huC
    · show dB.ρ ∈ Subgroup.normalizer (C : Set G)
      rw [h.ρ_eq]; exact hρC
  have hρ3 : dB.ρ ^ 3 ∈ Subgroup.centralizer (C : Set G) := by
    rw [h.ρ_eq]; exact Subgroup.centralizer_le hCX hρ3X
  have : Finite (dB.AuxGroup hL) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hNI : NoInvolutionsCentralizing C B :=
    CFSG.CGT.Stroth76.frame_noInvolutionsCentralizing_of_conj F h.A_le
      (fun b hb hb2 => h.mem_A_of_mul_self hb hb2) (hCX.trans hXS) hCB
      (fun z hz => (hCcX hz).2 _ F.uv_mem_V) (fun z hz => (hCcX hz).2 _ F.t_mem_V)
  obtain ⟨τ', D', huv', ht', hu₁, hρ'⟩ := hext (dB.toAux hL hBC.le hρ3) h.one_le_k hτ
    (dB.auxSub_mono hL hBC.le) (dB.auxSub_le_centralizer hL hCB)
    (by rw [dB.card_auxSub hL le_rfl, dB.card_auxSub hL hBC.le]; exact hcard)
    (fun x hx => by
      obtain ⟨n, hn, rfl⟩ := (dB.mem_auxSub hL).mp hx
      rw [← map_mul]
      exact (dB.inl_mem_auxSub hL).mpr (hsq n hn))
    (dB.toAux_L_le hL hBC.le hρ3)
    (dB.noInvolutionsCentralizing_auxSub hL hBC.le hNI le_rfl) le_rfl
  exact ⟨C, τ', dB.ofAux hL le_rfl D' huv' ht' hu₁ hρ',
    ⟨h.A_le.trans hBC.le, hCX.trans hXS, h.uv_eq, h.t_eq, h.u_eq, h.ρ_eq⟩, hBC, hCX⟩

theorem exists_typed_lt_le (hext : StrothExtStep) (hXc : IsMulCommutative X)
    (hXS : X ≤ (F.S : Subgroup G)) (huvX : F.dA.uv ∈ Subgroup.normalizer (X : Set G))
    (htX : F.dA.t ∈ Subgroup.normalizer (X : Set G))
    (huX : F.dA.u ∈ Subgroup.normalizer (X : Set G))
    (hρX : F.dA.ρ ∈ Subgroup.normalizer (X : Set G))
    (hρ3X : F.dA.ρ ^ 3 ∈ Subgroup.centralizer (X : Set G))
    {B : Subgroup G} {τ : StrothTypeIndex} {dB : StrothWeakTypeData B τ}
    (h : F.IsTyped B dB) (hBX : B < X) :
    ∃ (C : Subgroup G) (τ' : StrothTypeIndex) (dC : StrothWeakTypeData C τ'),
      F.IsTyped C dC ∧ B < C ∧ C ≤ X := by
  by_cases hτ : τ = StrothTypeIndex.t101 0
  · subst hτ
    have hcard : Nat.card B = Nat.card F.A := by
      rw [dB.card, F.card_A]
      rfl
    obtain rfl : F.A = B := Subgroup.eq_of_le_of_card_ge h.A_le hcard.le
    exact F.isTyped_A.exists_typed_lt_le_of_ne hext hXc hXS huvX htX huX hρX hρ3X
      (by intro h; cases h) hBX
  · exact h.exists_typed_lt_le_of_ne hext hXc hXS huvX htX huX hρX hρ3X hτ hBX

theorem exists_typed_of_le (hext : StrothExtStep) (hXc : IsMulCommutative X)
    (hXS : X ≤ (F.S : Subgroup G)) (huvX : F.dA.uv ∈ Subgroup.normalizer (X : Set G))
    (htX : F.dA.t ∈ Subgroup.normalizer (X : Set G))
    (huX : F.dA.u ∈ Subgroup.normalizer (X : Set G))
    (hρX : F.dA.ρ ∈ Subgroup.normalizer (X : Set G))
    (hρ3X : F.dA.ρ ^ 3 ∈ Subgroup.centralizer (X : Set G))
    {B : Subgroup G} {τ : StrothTypeIndex} {dB : StrothWeakTypeData B τ}
    (h : F.IsTyped B dB) (hBX : B ≤ X) :
    ∃ (τX : StrothTypeIndex) (dX : StrothWeakTypeData X τX), F.IsTyped X dX := by
  suffices key : ∀ n : ℕ, ∀ (B : Subgroup G) (τ : StrothTypeIndex) (dB : StrothWeakTypeData B τ),
      F.IsTyped B dB → B ≤ X → Nat.card X - Nat.card B = n →
      ∃ (τX : StrothTypeIndex) (dX : StrothWeakTypeData X τX), F.IsTyped X dX from
    key _ B τ dB h hBX rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B τ dB h hBX hn
    rcases eq_or_lt_of_le hBX with rfl | hlt
    · exact ⟨τ, dB, h⟩
    · obtain ⟨C, τ', dC, hC, hBC, hCX⟩ :=
        h.exists_typed_lt_le hext hXc hXS huvX htX huX hρX hρ3X hlt
      have h1 := Subgroup.card_lt_of_lt hBC
      have h2 := Subgroup.card_le_of_le hCX
      exact ih _ (by omega) C τ' dC hC hCX rfl

end StrothFrame.IsTyped

theorem StrothFrame.h223X_plus (hext : StrothExtStep) {G : Type} [Group G] [Finite G]
    (F : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
    (X : Subgroup G) (h : F.IsD D' dD')
    (hns : IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)))
    (hX : IsMulCommutative X) (hAX : F.A ≤ X)
    (hXR : X ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (hXV : ∀ x ∈ X, x⁻¹ * F.dA.uv * x * F.dA.uv⁻¹ ∈ D' ∧ x⁻¹ * F.dA.t * x * F.dA.t⁻¹ ∈ D')
    (hL : F.dA.L ≤ Subgroup.normalizer
      ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G))
    (huniq : ∀ Y : Subgroup G, Y ≤ X ⊔ D' → IsMulCommutative Y → Nat.card Y = Nat.card X →
      Y = X) :
    ∃ (F₁ : StrothFrame G) (D₁ : Subgroup G) (τ₁ : StrothTypeIndex)
      (dD₁ : StrothWeakTypeData D₁ τ₁), F₁.IsD D₁ dD₁ ∧
        IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
          ((F₁.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧
        Nat.card X ≤ Nat.card D₁ := by
  have hXS : X ≤ (F.S : Subgroup G) := hXR.trans (inf_le_left.trans inf_le_left)
  have hXN : X ≤ Subgroup.normalizer (D' : Set G) := hXR.trans (inf_le_left.trans inf_le_right)
  obtain ⟨o, hoE, hoD, hoodd, hρodd, hu, huvC, htC, huC, hρC, hρ3C⟩ :=
    h.exists_rho_change_X hns (F.S.2.to_le hXS) hXS hXN hXV hL
  have hnorm : ∀ g : G, g ∈ Subgroup.normalizer ((X ⊔ D' : Subgroup G) : Set G) →
      g ∈ Subgroup.normalizer (X : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ ?_ ?_ ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp (Subgroup.mem_sup_left hx)
    · exact Subgroup.map_isMulCommutative _ _
    · exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hoA : o ∈ Subgroup.centralizer (F.A : Set G) := Subgroup.centralizer_le h.A_le hoD
  set F' := F.withRho hoA hoE hoodd hρodd hu with hF'
  have hXS' : X ≤ (F'.S : Subgroup G) := hXS
  have huvX : F'.dA.uv ∈ Subgroup.normalizer (X : Set G) := hnorm _ huvC
  have htX : F'.dA.t ∈ Subgroup.normalizer (X : Set G) := hnorm _ htC
  have huX : F'.dA.u ∈ Subgroup.normalizer (X : Set G) := hnorm _ huC
  have hρX : F'.dA.ρ ∈ Subgroup.normalizer (X : Set G) := hnorm _ hρC
  have hXC : (X : Set G) ⊆ ((X ⊔ D' : Subgroup G) : Set G) := fun _ hx => Subgroup.mem_sup_left hx
  have hρ3X : F'.dA.ρ ^ 3 ∈ Subgroup.centralizer (X : Set G) := Subgroup.centralizer_le hXC hρ3C
  obtain ⟨τX, dX, hXT⟩ :=
    F'.isTyped_A.exists_typed_of_le hext hX hXS' huvX htX huX hρX hρ3X hAX
  exact hXT.exists_isD_isSylowIn_card_le hext

end CFSG.CGT.Stroth77
