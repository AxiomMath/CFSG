module

public import CFSG.GH74.GLS.Stage2.Local.P34NS12Main
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.GH74.GLS.TwoThin.Basic
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.Stage2.Local.P34NS CFSG.GorensteinWalter

section Norm

variable {G : Type} [Group G] [Finite G]

theorem normalizes_of_pgl {K : Subgroup G} {y : G} {q : ℕ}
    (hq : Odd q) (h5 : 5 ≤ q)
    (hL : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q))
    (hP : PGLModO K (zpowers y) q) : ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
  classical
  obtain ⟨hN, F₁, iF₁, fF₁, hF₁, ⟨e⟩⟩ := hP
  obtain ⟨F₀, iF₀, fF₀, hF₀, ⟨e₀⟩⟩ := hL
  set A : Subgroup G := K ⊔ zpowers y with hA
  set O' : Subgroup G := pPrimeCoreOf 2 K with hO'
  have hKA : K ≤ A := le_sup_left
  have hyA : y ∈ A := (le_sup_right : zpowers y ≤ A) (Subgroup.mem_zpowers y)
  have hO'K : O' ≤ K := TwoThin.pPrimeCoreOf_le K
  have hO'A : O' ≤ A := hO'K.trans hKA
  have hL0 : IVK.L2Field F₀ := ⟨by rw [hF₀]; exact hq, by rw [hF₀]; omega⟩
  have hL1 : IVK.L2Field F₁ := ⟨by rw [hF₁]; exact hq, by rw [hF₁]; omega⟩
  have hcardPSL : Nat.card (PSL2 F₁) = Nat.card (PSL2 F₀) := by
    rw [psl2_card_formula F₁ (IVK.isOddPrimePower_of_L2Field hL1), psl2_card_formula F₀ (IVK.isOddPrimePower_of_L2Field hL0), hF₀, hF₁]
  have hcardK : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = Nat.card (PSL2 F₀) :=
    Nat.card_congr (e₀.trans (IVK.L2.equivPSL F₀)).toEquiv
  have hcardAbar : Nat.card (↥A ⧸ O'.subgroupOf A) = 2 * Nat.card (PSL2 F₀) := by
    rw [Nat.card_congr e.toEquiv, IVK.card_pgl2_eq_two_mul hL1, hcardPSL]
  have hO'card : Nat.card ↥(O'.subgroupOf A) = Nat.card ↥(pPrimeCore 2 ↥K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'A).toEquiv, hO']
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hcardA : Nat.card ↥A = Nat.card ↥(pPrimeCore 2 ↥K) * (2 * Nat.card (PSL2 F₀)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (O'.subgroupOf A), hcardAbar, hO'card]
    ring
  have hcardK' : Nat.card ↥K = Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card (PSL2 F₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), hcardK]
    ring
  have hpos : 0 < Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card (PSL2 F₀) := by
    rw [← hcardK']
    exact Nat.card_pos
  have hidx : (K.subgroupOf A).index = 2 := by
    have h1 := Subgroup.index_mul_card (K.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv, hcardA, hcardK'] at h1
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hnormal : (K.subgroupOf A).Normal := Subgroup.normal_of_index_eq_two hidx
  have hAN : A ≤ normalizer (K : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).1 hnormal
  intro k hk
  have := (Subgroup.mem_normalizer_iff.1 (hAN hyA) k).1 hk
  exact this


end Norm

section Perfect

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) : ∀ c ∈ A ⊔ B, g * c * g⁻¹ ∈ A ⊔ B := by
  intro c hc
  rw [Subgroup.sup_eq_closure] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact Subgroup.subset_closure (Or.inl (hA y hy))
    · exact Subgroup.subset_closure (Or.inr (hB y hy))
  | one => simp
  | mul y w _ _ hy hw =>
    have e : g * (y * w) * g⁻¹ = (g * y * g⁻¹) * (g * w * g⁻¹) := by group
    rw [e]
    exact mul_mem hy hw
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hy

omit [Finite G] in
theorem R_sup_O_conj {N : Subgroup G} : ∀ n ∈ N, ∀ j ∈ oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N,
    n * j * n⁻¹ ∈ oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N :=
  fun _ hn j hj => conj_mem_sup (fun _ ha => oPrimeResidualOf_conj_mem N hn ha)
    (fun _ hb => TwoThin.pPrimeCoreOf_normalized N hn hb) j hj

omit [Finite G] in
theorem R_sup_O_le (N : Subgroup G) : oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N ≤ N :=
  sup_le (Subgroup.map_subtype_le _) (TwoThin.pPrimeCoreOf_le N)

omit [Finite G] in
theorem Jx_isPerfect (x : G) : ⁅Jx x, Jx x⁆ = Jx x := by
  have h : Group.IsPerfect ↥(Jx x) := by
    show Group.IsPerfect ↥(pLayerOf 2 (centralizer ({x} : Set G)))
    rw [pLayerOf_eq_map_P34]
    have : Group.IsPerfect ↥(pLayer ↥(centralizer ({x} : Set G)) 2) :=
      Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect _)
    exact Group.IsPerfect.map _
  exact Subgroup.isPerfect_iff.mp h

theorem perfect_le_R_sup_O {N P : Subgroup G} (hPN : P ≤ N) (hperf : ⁅P, P⁆ = P) :
    P ≤ oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N := by
  exact perfect_le_of_structure (N := N) (J := oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N)
    (O := ⊥) (R := oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N) (T := ⊥) (R_sup_O_le N) bot_le (R_sup_O_le N)
    R_sup_O_conj (fun _ _ o ho => by rw [Subgroup.mem_bot] at ho; subst ho; simp) R_sup_O_conj
    (by simp) inferInstance bot_le
    (by rw [sup_bot_eq]; exact not_two_dvd_relIndex_oPrimeResidual_sup) (by simp) hPN hperf

omit [Finite G] in
theorem mem_normalizer_of_involution {S : Subgroup G} {g : G} (hg2 : g * g = 1)
    (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g ∈ normalizer (S : Set G) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h1 s, fun hs => ?_⟩
  have := h1 _ hs
  rw [hinv] at this
  have e : g * (g * s * g) * g = s := by
    calc g * (g * s * g) * g = (g * g) * s * (g * g) := by group
      _ = s := by rw [hg2]; group
  rwa [e] at this

theorem Jx_le_sup {x y : G} {K : Subgroup G} (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (hKN : K ≤ centralizer ({x} : Set G)) (hyC : y ∈ centralizer ({x} : Set G))
    (hKy : ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hRO : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ zpowers x ⊔ (K ⊔ zpowers y)) :
    Jx x ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K := by
  set N : Subgroup G := centralizer ({x} : Set G) with hN
  set O : Subgroup G := pPrimeCoreOf 2 N with hO
  set Q : Subgroup G := O ⊔ zpowers x ⊔ (K ⊔ zpowers y) with hQ
  have hxN : x ∈ N := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hJQ : Jx x ≤ Q := hRO ▸ perfect_le_R_sup_O (Jx_le_centralizer x) (Jx_isPerfect x)
  have hxQ : x ∈ Q := (le_sup_right.trans le_sup_left : zpowers x ≤ Q) (Subgroup.mem_zpowers x)
  have hyQ : y ∈ Q := (le_sup_right.trans le_sup_right : zpowers y ≤ Q) (Subgroup.mem_zpowers y)
  have hOK : O ⊔ K ≤ Q := sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)
  have hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hKN hk)
    have e : x * k * x⁻¹ = k := by rw [← h]; group
    rwa [e]
  have hx_norm : x ∈ normalizer ((O ⊔ K : Subgroup G) : Set G) :=
    mem_normalizer_of_involution hx2 (conj_mem_sup (fun o ho => TwoThin.pPrimeCoreOf_normalized N hxN ho) hxK)
  have hy_norm : y ∈ normalizer ((O ⊔ K : Subgroup G) : Set G) :=
    mem_normalizer_of_involution hy2 (conj_mem_sup (fun o ho => TwoThin.pPrimeCoreOf_normalized N hyC ho) hKy)
  have hQnorm : Q ≤ normalizer ((O ⊔ K : Subgroup G) : Set G) :=
    sup_le (sup_le (le_sup_left.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).2 hx_norm))
      (sup_le (le_sup_right.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).2 hy_norm))
  have hconj : ∀ n ∈ Q, ∀ j ∈ O ⊔ K, n * j * n⁻¹ ∈ O ⊔ K := fun n hn j hj =>
    (Subgroup.mem_normalizer_iff.1 (hQnorm hn) j).1 hj
  have hTN : Subgroup.closure ({x, y} : Set G) ≤ Q :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxQ, Set.singleton_subset_iff.2 hyQ⟩)
  have hf : Q ⊔ ⊥ ≤ ⊥ ⊔ (O ⊔ K) ⊔ Subgroup.closure ({x, y} : Set G) := by
    rw [sup_bot_eq, bot_sup_eq]
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) (sup_le (le_sup_right.trans le_sup_left) ?_)
    · exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Set.mem_insert x {y})) |>.trans le_sup_right
    · exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))) |>.trans le_sup_right
  exact perfect_le_of_structure (N := Q) (J := O ⊔ K) (O := ⊥) (R := Q)
    (T := Subgroup.closure ({x, y} : Set G)) hOK bot_le le_rfl hconj
    (fun _ _ o ho => by rw [Subgroup.mem_bot] at ho; subst ho; simp)
    (fun n hn r hr => Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hr) (Subgroup.inv_mem _ hn))
    (by simp) (isSolvable_closure_pair hxy) hTN (by simp) hf hJQ (Jx_isPerfect x)

end Perfect


section Iso

variable {G : Type} [Group G] [Finite G]

theorem isL2_Jx {x : G} {K : Subgroup G} {q : ℕ}
    (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hKJ : K ≤ Jx x)
    (hJ : Jx x ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ K)
    (hL : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q)) :
    IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := centralizer ({x} : Set G) with hN
  have hKN : K ≤ N := hKc.1
  have hJN : Jx x ≤ N := Jx_le_centralizer x
  have hKsub : (K.subgroupOf N).IsSubnormal := by
    obtain ⟨_, _, hs, _⟩ := hKc.2
    exact hs
  have hJsub : ((Jx x).subgroupOf N).IsSubnormal :=
    (normal_subgroupOf_of_conj (Jx_normalized x)).isSubnormal
  obtain ⟨eK, -⟩ := CFSG.ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hKN hKsub
  obtain ⟨eJ, -⟩ := CFSG.ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hJN hJsub
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥N) with hπ
  have hO : (pPrimeCoreOf 2 N).subgroupOf N = pPrimeCore 2 ↥N := by
    unfold pPrimeCoreOf
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have himg : ((Jx x).subgroupOf N).map π = (K.subgroupOf N).map π := by
    apply le_antisymm
    · calc ((Jx x).subgroupOf N).map π ≤ ((pPrimeCoreOf 2 N ⊔ K).subgroupOf N).map π :=
            Subgroup.map_mono (Subgroup.comap_mono hJ)
        _ = (pPrimeCore 2 ↥N ⊔ K.subgroupOf N).map π := by
            rw [Subgroup.subgroupOf_sup (TwoThin.pPrimeCoreOf_le N) hKN, hO]
        _ = (K.subgroupOf N).map π := by
            rw [Subgroup.map_sup]
            have : (pPrimeCore 2 ↥N).map π = ⊥ := by
              rw [hπ]
              exact (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk'])
            rw [this, bot_sup_eq]
    · exact Subgroup.map_mono (Subgroup.comap_mono hKJ)
  obtain ⟨F₀, iF₀, fF₀, hq, ⟨e₀⟩⟩ := hL
  exact ⟨F₀, iF₀, fF₀, hq, ⟨(eJ.trans ((MulEquiv.subgroupCongr himg).trans eK.symm)).trans e₀⟩⟩


end Iso

end CFSG.GH74.GLS.Stage2.Local.P27M12
