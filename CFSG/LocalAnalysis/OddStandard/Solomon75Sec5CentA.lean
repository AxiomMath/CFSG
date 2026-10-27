module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentTrans
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentMirror

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Aux

variable {X : Type} [Group X]

theorem exists_pow_mul_eq_of_normalizes {P : Subgroup X} {o w : X} (ho : o ∈ P)
    (hw : w ∈ normalizer (P : Set X)) (m : ℕ) : ∃ p ∈ P, (o * w) ^ m = p * w ^ m := by
  induction m with
  | zero => exact ⟨1, P.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp, h⟩ := ih
    refine ⟨p * (w ^ m * o * (w ^ m)⁻¹), P.mul_mem hp ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 ((normalizer (P : Set X)).pow_mem hw m) o).1 ho
    · rw [pow_succ, h, pow_succ]; group

theorem exists_pow_two_mem_of_mem_sup {P W : Subgroup X} (hWP : W ≤ normalizer (P : Set X))
    (hW : IsPGroup 2 ↥W) {v : X} (hv : v ∈ P ⊔ W) : ∃ k : ℕ, v ^ (2 ^ k) ∈ P := by
  obtain ⟨o, ho, w, hw, hov⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing P W hWP v).1 hv
  subst hov
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hk' : w ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨p, hp, h⟩ := exists_pow_mul_eq_of_normalizes ho (hWP hw) (2 ^ k)
  exact ⟨k, by rw [h, hk', mul_one]; exact hp⟩

end Aux

section Core

variable {X : Type} [Group X] [Finite X]

theorem commutator_image_central {n : ℕ} (hn : 5 ≤ n) {A E₁ 𝒪 W : Subgroup X} {s : X}
    (hsA : s ∈ normalizer (A : Set X)) (C : AhatData.CoverSetup n (↥A ⧸ pPrimeCore 2 ↥A))
    (hEA : E₁ ≤ A) (hcov : E₁.subgroupOf A ⊔ pPrimeCore 2 ↥A = ⊤)
    (hsE : ∀ x ∈ E₁, s * x * s⁻¹ ∈ E₁) (h𝒪 : Odd (Nat.card 𝒪))
    (hE𝒪 : E₁ ≤ normalizer (𝒪 : Set X)) (hW : IsPGroup 2 ↥W) (hW𝒪 : W ≤ normalizer (𝒪 : Set X))
    (hV : ∀ x ∈ E₁, ⁅x, s⁆ ∈ 𝒪 ⊔ W) :
    ∀ y : ↥A ⧸ pPrimeCore 2 ↥A, quotConj hsA y * y⁻¹ ∈ Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A) := by
  classical
  set K := ↥A ⧸ pPrimeCore 2 ↥A with hK
  let ψ : ↥E₁ →* K := (QuotientGroup.mk' (pPrimeCore 2 ↥A)).comp (Subgroup.inclusion hEA)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have ha : a ∈ E₁.subgroupOf A ⊔ pPrimeCore 2 ↥A := by rw [hcov]; exact Subgroup.mem_top a
    obtain ⟨e, he, o, ho, hea⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    refine ⟨⟨(e : X), he⟩, ?_⟩
    show (QuotientGroup.mk (⟨(e : X), hEA he⟩ : ↥A) : K) = QuotientGroup.mk a
    rw [← hea, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
  have hmem : ∀ x : ↥E₁, ⁅(x : X), s⁆ ∈ E₁ := by
    intro x
    have e : ⁅(x : X), s⁆ = x * (s * (x : X)⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact E₁.mul_mem x.2 (hsE _ (E₁.inv_mem x.2))
  let f : ↥E₁ → ↥E₁ := fun x => ⟨⁅(x : X), s⁆, hmem x⟩
  let T : Subgroup ↥E₁ := Subgroup.closure (Set.range f)
  have hfmul : ∀ e x : ↥E₁, e * f x * e⁻¹ = f (e * x) * (f e)⁻¹ := by
    intro e x
    apply Subtype.ext
    simp only [f, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  have hTn : T.Normal := by
    refine ⟨fun t ht e => ?_⟩
    induction ht using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, rfl⟩ := hg
      rw [hfmul]
      exact T.mul_mem (Subgroup.subset_closure ⟨_, rfl⟩)
        (T.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩))
    | one => simp
    | mul a b _ _ ha hb =>
      have : e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
      rw [this]; exact T.mul_mem ha hb
    | inv a _ ha =>
      have : e * a⁻¹ * e⁻¹ = (e * a * e⁻¹)⁻¹ := by group
      rw [this]; exact T.inv_mem ha
  have hTbar : (T.map ψ).Normal := Subgroup.Normal.map hTn ψ hψ
  let V : Subgroup X := 𝒪 ⊔ W
  have hTV : ∀ t ∈ T, ((t : ↥E₁) : X) ∈ V := by
    intro t ht
    have : T ≤ V.comap E₁.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      exact hV x x.2
    exact this ht
  let O' : Subgroup ↥E₁ := 𝒪.comap E₁.subtype
  have hO'n : O'.Normal := ⟨fun o ho e => by
    show ((e * o * e⁻¹ : ↥E₁) : X) ∈ 𝒪
    have := (Subgroup.mem_normalizer_iff.1 (hE𝒪 e.2) (o : X)).1 ho
    simpa using this⟩
  let R : Subgroup ↥E₁ := T ⊓ O'
  have hRn : R.Normal := inferInstance
  have hRbar : (R.map ψ).Normal := Subgroup.Normal.map hRn ψ hψ
  have hRodd : Odd (Nat.card (R.map ψ)) := by
    refine Odd.of_dvd_nat h𝒪 ((Subgroup.card_map_dvd R ψ).trans ?_)
    let g : R →* ↥𝒪 := ⟨⟨fun r => ⟨((r : ↥E₁) : X), r.2.2⟩, rfl⟩, fun a b => rfl⟩
    have hg : Function.Injective g := fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥𝒪 => (w : X)) h
    exact Subgroup.card_dvd_of_injective g hg
  have hRbot : R.map ψ = ⊥ := C.normal_odd_eq_bot hn hRodd
  have hTp : IsPGroup 2 ↥(T.map ψ) := by
    intro g
    obtain ⟨_, ⟨t, ht, rfl⟩⟩ := g
    obtain ⟨k, hk⟩ := exists_pow_two_mem_of_mem_sup hW𝒪 hW (hTV t ht)
    refine ⟨k, ?_⟩
    have htk : t ^ (2 ^ k) ∈ R := ⟨T.pow_mem ht _, hk⟩
    have : ψ (t ^ (2 ^ k)) ∈ R.map ψ := ⟨_, htk, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at this
    apply Subtype.ext
    simpa [map_pow] using this
  have hcen : T.map ψ ≤ Subgroup.center K := C.normal_pgroup_le_center hn hTp
  intro y
  obtain ⟨x, rfl⟩ := hψ y
  have hx : quotConj hsA (ψ x) = (ψ (f x))⁻¹ * ψ x := by
    have h1 : quotConj hsA (ψ x) = QuotientGroup.mk (conjAut hsA ⟨(x : X), hEA x.2⟩) :=
      QuotientGroup.congr_mk _ _ _ _ _
    have h2 : conjAut hsA ⟨(x : X), hEA x.2⟩ =
        (⟨⁅(x : X), s⁆, hEA (hmem x)⟩ : ↥A)⁻¹ * ⟨(x : X), hEA x.2⟩ := by
      apply Subtype.ext
      simp only [coe_conjAut, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rfl
  have hf : ψ (f x) ∈ Subgroup.center K := hcen ⟨f x, Subgroup.subset_closure ⟨x, rfl⟩, rfl⟩
  have hfinal : (ψ (f x))⁻¹ * ψ x * (ψ x)⁻¹ = (ψ (f x))⁻¹ := by group
  rw [hx, hfinal]
  exact (Subgroup.center K).inv_mem hf

end Core

section Main

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem commutator_decomp_of_mirror {s r : X} {Zs : Subgroup X} (hsZs : s ∈ Zs)
    (hrs : r * s = s * r)
    (hL34 : LPlusIn (centralizer ({r} : Set X)) =
      pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) ⊔
        (normalizer (Zs : Set X) ⊓ LPlusIn (centralizer ({r} : Set X))))
    {x : X} (hx : x ∈ LPlusIn (centralizer ({r} : Set X))) :
    ∃ o ∈ pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))),
      ∃ w ∈ Zs ⊓ centralizer ({r} : Set X), ⁅x, s⁆ = o * w := by
  set L : Subgroup X := LPlusIn (centralizer ({r} : Set X)) with hL
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 L with h𝒪
  have hLC : L ≤ centralizer ({r} : Set X) := LPlusIn_le _
  have hCn : centralizer ({r} : Set X) ≤ normalizer (𝒪 : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf L)
  have hsC : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
  have hx' : x ∈ 𝒪 ⊔ (normalizer (Zs : Set X) ⊓ L) := by rw [← hL34]; exact hx
  obtain ⟨o, ho, y, hy, hxy⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing 𝒪
    (normalizer (Zs : Set X) ⊓ L) (fun y hy => hCn (hLC hy.2)) x).1 hx'
  have hw'Zs : y * s * y⁻¹ ∈ Zs := (Subgroup.mem_normalizer_iff.1 hy.1 s).1 hsZs
  have hw'C : y * s * y⁻¹ ∈ centralizer ({r} : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLC hy.2) hsC) (Subgroup.inv_mem _ (hLC hy.2))
  refine ⟨o * ((y * s * y⁻¹) * o⁻¹ * (y * s * y⁻¹)⁻¹), 𝒪.mul_mem ho ?_, (y * s * y⁻¹) * s⁻¹,
    ⟨Zs.mul_mem hw'Zs (Zs.inv_mem hsZs), Subgroup.mul_mem _ hw'C (Subgroup.inv_mem _ hsC)⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (hCn hw'C) o⁻¹).1 (𝒪.inv_mem ho)
  · rw [← hxy]; simp only [commutatorElement_def]; group

theorem sec5_a_of_centralizes (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {Aj : Subgroup X}
    (hAj : Sec5Comp X n (normalizer (Z : Set X)) Aj) {r : X} (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hrs : r * s = s * r) (hscj : r ∈ centralizerSection Aj (pPrimeCoreOf 2 Aj)) :
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) = ⊥ := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  have hr2s : r ^ 2 = 1 := by rw [sq]; exact hr2
  have hr2' : orderOf r = 2 := orderOf_eq_prime hr2s hr1
  have hsAj : s ∈ normalizer (Aj : Set X) :=
    mem_normalizer_of_map_conj_eq (hN X n z Z S h s hs Aj hAj)
  set M : AhatModel X n Aj := AhatModel.ofCover hAj.2 with hM
  have hperm : M.perm s hsAj ≠ 1 := by
    intro h1
    have h3 := ((hF X n z Z S h s hs).1 Aj hAj hsAj M).1
    rw [h1] at h3
    have h8 : fixCount (1 : Perm (Fin n)) = n := by
      unfold fixCount; simp
    omega
  by_contra hcon
  obtain ⟨Zs, hZs, hrZs, -⟩ := exists_mirror_sylow_normalized X n (s := s)
    (B := Subgroup.zpowers r) (aux_isPGroup_zpowers_of_sq hr2s)
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hrs))
  obtain ⟨g, S₁, -, -, -, hS₁⟩ := h.exists_mirror_of_sylow hs hZs
  have hrNs : r ∈ normalizer (Zs : Set X) := hrZs (Subgroup.mem_zpowers r)
  have hJ := exists_K0_normalizer_inf_ne_bot hS₁ hr2' hrs hrNs hcon
  have hL34 := hS₁.l52.c r hrNs hr2' hJ
  obtain ⟨u₀, hu₀⟩ := hAj.1
  obtain ⟨u, hu, huC⟩ := hu₀.exists_witness_centralizer_singleton hr2s hscj
  obtain ⟨hd1, hd2, -⟩ := hu.descend_singleton hAj.2 hr2s hscj huC
  set A' : Subgroup X := oTwoPrimeOf (Aj ⊓ centralizer ({r} : Set X)) with hA'
  obtain ⟨Mr, hMr, -, hEMr⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := r) hr2'
    (inf_le_right : normalizer (Z : Set X) ⊓ centralizer ({r} : Set X) ≤
      centralizer ({r} : Set X)) hd1 hd2
  set E₀ : Subgroup X := oTwoPrimeOf (A' ⊓ centralizer ({u} : Set X)) with hE₀
  obtain ⟨hE₀A', hcovA', -⟩ := hd1.cover_oTwoPrimeOf
  have hA'Aj : A' ≤ Aj := (oTwoPrimeOf_le _).trans inf_le_left
  have hE₀Aj : E₀ ≤ Aj := hE₀A'.trans hA'Aj
  have hE₀L : E₀ ≤ LPlusIn (centralizer ({r} : Set X)) := hEMr.trans hMr.le_LPlusIn
  have hcov₀ : E₀.subgroupOf Aj ⊔ pPrimeCore 2 ↥Aj = ⊤ := by
    have hE₀c : IsDoubleCoverOfAlt (↥E₀ ⧸ pPrimeCore 2 ↥E₀) n :=
      (isDoubleCoverOfAlt_quot_iff_of_covers hE₀A' hcovA' n).2 hd2
    refine covers_of_card_le hE₀Aj ?_
    rw [natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hAj.2,
      natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hE₀c]
  set E₁ : Subgroup X := Aj ⊓ LPlusIn (centralizer ({r} : Set X)) with hE₁
  have hE₀E₁ : E₀ ≤ E₁ := le_inf hE₀Aj hE₀L
  have hcov₁ : E₁.subgroupOf Aj ⊔ pPrimeCore 2 ↥Aj = ⊤ :=
    le_antisymm le_top (hcov₀.ge.trans (sup_le_sup_right (Subgroup.subgroupOf_mono Aj hE₀E₁) _))
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) with h𝒪
  have hCn : centralizer ({r} : Set X) ≤ normalizer (𝒪 : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hsC : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
  have hE₁L : ∀ x ∈ E₁, x ∈ LPlusIn (centralizer ({r} : Set X)) := fun x hx => hx.2
  have hE₁𝒪 : E₁ ≤ normalizer (𝒪 : Set X) := fun x hx =>
    hCn (LPlusIn_le _ (hE₁L x hx))
  have hsE : ∀ x ∈ E₁, s * x * s⁻¹ ∈ E₁ := fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 hsAj x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_LPlusIn _ hsC) x).1 hx.2⟩
  have hV : ∀ x ∈ E₁, ⁅x, s⁆ ∈ 𝒪 ⊔ (Zs ⊓ centralizer ({r} : Set X)) := by
    intro x hx
    obtain ⟨o, ho, w, hw, hxs⟩ := commutator_decomp_of_mirror hS₁.pair.mem hrs hL34 (hE₁L x hx)
    rw [hxs]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hw)
  have hW : IsPGroup 2 ↥(Zs ⊓ centralizer ({r} : Set X)) :=
    hS₁.isPGroup_Z.to_le inf_le_left
  have hcentral := commutator_image_central (n := n) (by omega) hsAj M.C inf_le_left hcov₁ hsE
    (odd_card_oddCoreOf _) hE₁𝒪 hW (inf_le_right.trans hCn) hV
  exact hperm (M.perm_eq_one_of_commutator_central hn hsAj hcentral)

theorem sec5_a_prime (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (h : Sec5Data X n z Z S)
    (hk : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂)
    {s : X} (hs : IsSec5Inv X Z s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {r : X} (hrA : r ∈ A) (hr1 : r ≠ 1)
    (hr2 : r * r = 1) (hrs : r * s = s * r) :
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) = ⊥ := by
  have hrN : r ∈ normalizer ((normalizer (Z : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_normalizer (hA.isPCompIn.1 hrA)
  obtain ⟨Aj, hAj, hne⟩ : ∃ Aj : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) Aj ∧
      Aj ≠ A := by
    obtain ⟨A₁, A₂, h₁, h₂, h12⟩ := hk
    by_cases h1A : A₁ = A
    · exact ⟨A₂, h₂, fun h => h12 (h1A.trans h.symm)⟩
    · exact ⟨A₁, h₁, h1A⟩
  exact sec5_a_of_centralizes hF hN h hs hAj hr1 hr2 hrs
    (normalizes_isPCompIn_of_comm_mem hAj.isPCompIn hrN (fun l hl =>
      commutator_mem_oddCoreOf_of_ne hAj.isPCompIn hA.isPCompIn hne hl hrA))

end Main

end CFSG.OddStandard.Solomon75
