module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCPar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Char
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
  CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Pointwise

section Conj

variable {F : Type} [Field F]

theorem k4_conj_radP {a b a' b' : F} (h : ¬ (a = 0 ∧ b = 0)) (h' : ¬ (a' = 0 ∧ b' = 0)) :
    ∃ g ∈ CenD F, g * elP a b * g⁻¹ = elP a' b' := by
  have hu : (![a, b] : Fin 2 → F) ≠ 0 := fun hz =>
    h ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  have hx : (![a', b'] : Fin 2 → F) ≠ 0 := fun hz =>
    h' ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  obtain ⟨A, hA⟩ := exists_sl2_vecMul hu hx
  have h0 := congrFun hA 0
  have h1 := congrFun hA 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
  refine ⟨(bSL A)⁻¹, inv_mem (bSL_mem_CenD A), ?_⟩
  rw [inv_inv, mul_assoc, elP_mul_bSL, ← mul_assoc, inv_mul_cancel, one_mul, h0, h1]

theorem k4_conj_radM {a b a' b' : F} (h : ¬ (a = 0 ∧ b = 0)) (h' : ¬ (a' = 0 ∧ b' = 0)) :
    ∃ g ∈ CenD F, g * elM a b * g⁻¹ = elM a' b' := by
  have hu : (![a, b] : Fin 2 → F) ≠ 0 := fun hz =>
    h ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  have hx : (![a', b'] : Fin 2 → F) ≠ 0 := fun hz =>
    h' ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  obtain ⟨A, hA⟩ := exists_sl2_mulVec hu hx
  have h0 := congrFun hA 0
  have h1 := congrFun hA 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  refine ⟨bSL A, bSL_mem_CenD A, ?_⟩
  rw [bSL_mul_elM, mul_assoc, mul_inv_cancel, mul_one, h0, h1]

end Conj

section Core

variable {G₀ H : Type*} [Group G₀] [Group H]

theorem k4_transitive_core (φ : G₀ →* H) {X₀ C₀ P₀ : Subgroup G₀}
    (hdec : ∀ k ∈ P₀, ∃ x ∈ X₀, ∃ c ∈ C₀, k = x * c)
    (hnorm : ∀ c ∈ C₀, ∀ t ∈ X₀, c * t * c⁻¹ ∈ X₀)
    (hcomm : ∀ s ∈ X₀.map φ, ∀ t ∈ X₀.map φ, s * t = t * s)
    (hconj : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ X₀, y ≠ 1 → ∃ g ∈ P₀.map φ, g * φ x * g⁻¹ = φ y)
    (hinj : ∀ x ∈ X₀, ∀ y ∈ X₀, φ x = φ y → x = y) :
    ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ X₀, y ≠ 1 → ∃ c ∈ C₀, c * x * c⁻¹ = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨g, ⟨k, hk, rfl⟩, hg⟩ := hconj x hx hx1 y hy hy1
  obtain ⟨x', hx', c, hc, rfl⟩ := hdec k hk
  refine ⟨c, hc, hinj _ (hnorm c hc x hx) y hy ?_⟩
  have hcm := hcomm (φ x') (Subgroup.mem_map_of_mem φ hx') (φ y) (Subgroup.mem_map_of_mem φ hy)
  have h1 : φ (c * x * c⁻¹) =
      (φ x')⁻¹ * (φ (x' * c) * φ x * (φ (x' * c))⁻¹) * φ x' := by
    simp only [map_mul, map_inv]
    group
  rw [h1, hg, mul_assoc, ← hcm, inv_mul_cancel_left]

end Core

section Model

variable {G₀ : Type} [Group G₀] {F : Type} [Field F]

theorem k4_transitive_of_rad (φ : G₀ →* projectiveSL 3 F) {X₀ C₀ P₀ : Subgroup G₀}
    (R : Subgroup SL(3, F)) (el : F → F → SL(3, F))
    (hRel : ∀ g ∈ R, ∃ a b : F, g = el a b) (hel0 : el 0 0 = 1)
    (hmul : ∀ a b a' b' : F, el a b * el a' b' = el (a + a') (b + b'))
    (hcon : ∀ a b a' b' : F, ¬ (a = 0 ∧ b = 0) → ¬ (a' = 0 ∧ b' = 0) →
      ∃ g ∈ CenD F, g * el a b * g⁻¹ = el a' b')
    (hdec : ∀ k ∈ P₀, ∃ x ∈ X₀, ∃ c ∈ C₀, k = x * c)
    (hnorm : ∀ c ∈ C₀, ∀ t ∈ X₀, c * t * c⁻¹ ∈ X₀)
    (hCenD : ∀ g ∈ CenD F, proj 3 F g ∈ P₀.map φ)
    (hX : X₀.map φ = R.map (proj 3 F))
    (hinj : ∀ x ∈ X₀, ∀ y ∈ X₀, φ x = φ y → x = y) :
    ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ X₀, y ≠ 1 → ∃ c ∈ C₀, c * x * c⁻¹ = y := by
  have hpre : ∀ x ∈ X₀, ∃ a b : F, proj 3 F (el a b) = φ x := by
    intro x hx
    have hx' : φ x ∈ R.map (proj 3 F) := hX ▸ Subgroup.mem_map_of_mem φ hx
    obtain ⟨g, hg, hgx⟩ := hx'
    obtain ⟨a, b, rfl⟩ := hRel g hg
    exact ⟨a, b, hgx⟩
  have hnz : ∀ x ∈ X₀, x ≠ 1 → ∀ a b : F, proj 3 F (el a b) = φ x → ¬ (a = 0 ∧ b = 0) := by
    rintro x hx hx1 a b hab ⟨rfl, rfl⟩
    apply hx1
    refine hinj x hx 1 (one_mem _) ?_
    rw [← hab, hel0, map_one, map_one]
  refine k4_transitive_core φ hdec hnorm ?_ ?_ hinj
  · intro s hs t ht
    rw [hX] at hs ht
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨g', hg', rfl⟩ := ht
    obtain ⟨a, b, rfl⟩ := hRel g hg
    obtain ⟨a', b', rfl⟩ := hRel g' hg'
    rw [← map_mul, ← map_mul, hmul, hmul, add_comm a, add_comm b]
  · intro x hx hx1 y hy hy1
    obtain ⟨a, b, hab⟩ := hpre x hx
    obtain ⟨a', b', hab'⟩ := hpre y hy
    obtain ⟨g, hg, hgc⟩ := hcon a b a' b' (hnz x hx hx1 a b hab) (hnz y hy hy1 a' b' hab')
    refine ⟨proj 3 F g, hCenD g hg, ?_⟩
    rw [← hab, ← hab', ← map_inv, ← map_mul, ← map_mul, hgc]

theorem k4_transitive_of_model (φ : G₀ →* projectiveSL 3 F) {X₀ C₀ P₀ : Subgroup G₀}
    (hdec : ∀ k ∈ P₀, ∃ x ∈ X₀, ∃ c ∈ C₀, k = x * c)
    (hnorm : ∀ c ∈ C₀, ∀ t ∈ X₀, c * t * c⁻¹ ∈ X₀)
    (hCenD : ∀ g ∈ CenD F, proj 3 F g ∈ P₀.map φ)
    (hX : X₀.map φ = (radP F).map (proj 3 F) ∨ X₀.map φ = (radM F).map (proj 3 F))
    (hinj : ∀ x ∈ X₀, ∀ y ∈ X₀, φ x = φ y → x = y) :
    ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ X₀, y ≠ 1 → ∃ c ∈ C₀, c * x * c⁻¹ = y := by
  rcases hX with hX | hX
  · exact k4_transitive_of_rad φ (radP F) elP (fun g hg => mem_radP.mp hg) elP_zero elP_mul
      (fun _ _ _ _ h h' => k4_conj_radP h h') hdec hnorm hCenD hX hinj
  · exact k4_transitive_of_rad φ (radM F) elM (fun g hg => mem_radM.mp hg) elM_zero elM_mul
      (fun _ _ _ _ h h' => k4_conj_radM h h') hdec hnorm hCenD hX hinj

end Model

section Center

variable {G : Type*} [Group G]

theorem k4_mulAut_mem_center (e : MulAut G) {z : G} (hz : z ∈ Subgroup.center G) :
    e z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, hz g']

end Center

section Main

theorem c43c_transitive {Q : Type} [Group Q] [Finite Q] {z : Q} {p : ℕ} {X : Subgroup Q}
    (hp : p.Prime) (hp2 : p ≠ 2) (hc : C43c z p X) :
    ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 →
      ∃ c ∈ ncl X ⊓ Subgroup.centralizer ({z} : Set Q), c * x * c⁻¹ = y := by
  obtain ⟨n, hn, hLie, hXz, hmax, hOp, hel, hcard⟩ := hc
  have hpp : Fact p.Prime := ⟨hp⟩
  have hXK : X ≤ ncl X := (le_sup_left : X ≤ X ⊔ zpowers z).trans hXz
  have hKn : (ncl X).Normal := Subgroup.normalClosure_normal
  obtain ⟨F, iF, fF, hFcard, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hpF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p (by omega)
  have hchar : CharP F p := charP_of_dvd_card p hpF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp h'))
  set K : Subgroup Q := ncl X
  let φ : ↥K →* projectiveSL 3 F :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hs : Function.Surjective φ := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerφ : φ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    show ι (QuotientGroup.mk k) = 1 ↔ _
    rw [map_eq_one_iff ι ι.injective, QuotientGroup.eq_one_iff]
  set C : Subgroup Q := K ⊓ centralizer ({z} : Set Q)
  set P : Subgroup Q := X ⊔ C
  have hPar : ParData ↥K p (P.subgroupOf K) := parData_of_isMaxParabolicP hmax
  have hXpg : IsPGroup p ↥X := IsElementaryAbelian.isPGroup p ↥X
  set X₀ : Subgroup ↥K := X.subgroupOf K
  have hXp : IsPGroup p ↥X₀ :=
    hXpg.of_injective (Subgroup.subgroupOfEquivOfLe hXK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXK).injective
  have hPnorm : P ≤ normalizer (X : Set Q) := by
    rw [hOp]
    exact le_normalizer_Op p P
  have hXP : P.subgroupOf K ≤ normalizer (X₀ : Set ↥K) := by
    intro k hk
    have hkP : (k : Q) ∈ P := hk
    have hkX := hPnorm hkP
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hkX (x : Q)
  have hXne : X₀.map φ ≠ ⊥ := by
    intro hbot
    have hXc : X₀ ≤ Subgroup.center ↥K := by
      intro x hx
      have : φ x ∈ X₀.map φ := Subgroup.mem_map_of_mem φ hx
      rw [hbot, Subgroup.mem_bot] at this
      rw [← hkerφ]
      exact this
    set Zc : Subgroup Q := (Subgroup.center ↥K).map K.subtype
    have hZn : Zc.Normal := ⟨fun n hn g => by
      obtain ⟨z₀, hz₀, rfl⟩ := hn
      refine ⟨MulAut.conjNormal g z₀, k4_mulAut_mem_center (MulAut.conjNormal g) hz₀, ?_⟩
      exact MulAut.conjNormal_apply g z₀⟩
    have hXZ : (X : Set Q) ⊆ Zc := by
      intro x hx
      exact ⟨⟨x, hXK hx⟩, hXc (show (⟨x, hXK hx⟩ : ↥K) ∈ X₀ from hx), rfl⟩
    have hKZ : K ≤ Zc := Subgroup.normalClosure_le_normal hXZ
    have hcentral : ∀ k : ↥K, k ∈ Subgroup.center ↥K := by
      intro k
      obtain ⟨z₀, hz₀, hz₀k⟩ := hKZ k.2
      have : z₀ = k := Subtype.ext hz₀k
      exact this ▸ hz₀
    have hone : proj 3 F (elP 1 0) = 1 := by
      obtain ⟨k, hk⟩ := hs (proj 3 F (elP 1 0))
      rw [← hk]
      have : k ∈ φ.ker := by rw [hkerφ]; exact hcentral k
      exact this
    have := eq_zero_of_elP_mem_scalars (proj_eq_one_iff.mp hone)
    exact one_ne_zero this.1
  obtain ⟨h, hh⟩ := exists_conj_std p (map_mem_maximalParabolics hs hkerφ.le hPar)
  set cj : MulAut (projectiveSL 3 F) := MulAut.conj h
  set φ₁ : ↥K →* projectiveSL 3 F := cj.toMonoidHom.comp φ with hφ₁
  obtain ⟨W₀, hW₀, hP₁⟩ : ∃ W₀ : Submodule F (Fin 3 → F), (W₀ = vPlus F ∨ W₀ = vMinus F) ∧
      (P.subgroupOf K).map φ₁ = projStabilizer W₀ := by
    rcases hh with hh | hh
    · exact ⟨vPlus F, Or.inl rfl, by rw [hφ₁, ← Subgroup.map_map]; exact hh⟩
    · exact ⟨vMinus F, Or.inr rfl, by rw [hφ₁, ← Subgroup.map_map]; exact hh⟩
  have hXne₁ : X₀.map φ₁ ≠ ⊥ := by
    intro h'
    apply hXne
    refine Subgroup.map_injective (f := cj.toMonoidHom) cj.injective ?_
    rw [Subgroup.map_bot, ← h', hφ₁, Subgroup.map_map]
  have hCenD : ∀ g ∈ CenD F, proj 3 F g ∈ (P.subgroupOf K).map φ₁ := by
    intro g hg
    rw [hP₁]
    refine Subgroup.mem_map_of_mem _ ?_
    rcases hW₀ with rfl | rfl
    · exact CenD_le_stabilizer_vPlus h2 hg
    · exact CenD_le_stabilizer_vMinus h2 hg
  have hCen : ∀ g ∈ CenD F, proj 3 F g ∈ normalizer ((X₀.map φ₁ : Subgroup _) : Set _) := by
    intro g hg
    obtain ⟨k, hk, hkg⟩ := hCenD g hg
    rw [← hkg]
    exact le_normalizer_map φ₁ ⟨k, hXP hk, rfl⟩
  have hX : X₀.map φ₁ = (radP F).map (proj 3 F) ∨ X₀.map φ₁ = (radM F).map (proj 3 F) :=
    classify_p_subgroup h2 p (X₀.map φ₁) (hXp.map φ₁) hXne₁ hCen
  have hXcard : Nat.card ↥X₀ = p ^ (2 * n) := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  have hmapcard : Nat.card ↥(X₀.map φ₁) = p ^ (2 * n) := by
    have hFsq : Nat.card F ^ 2 = p ^ (2 * n) := by
      rw [hFcard, ← pow_mul, mul_comm]
    rw [← hFsq]
    rcases hX with hX | hX
    · rw [hX]
      have e : (radP F).map (proj 3 F) = ((proj 3 F).comp (elPHom F)).range := by
        rw [MonoidHom.range_comp]
        rfl
      rw [e]
      exact card_range_eq _ proj_elPHom_injective
    · rw [hX]
      have e : (radM F).map (proj 3 F) = ((proj 3 F).comp (elMHom F)).range := by
        rw [MonoidHom.range_comp]
        rfl
      rw [e]
      exact card_range_eq _ proj_elMHom_injective
  have hinj : ∀ x ∈ X₀, ∀ y ∈ X₀, φ₁ x = φ₁ y → x = y := by
    have hbij : Function.Bijective (φ₁.subgroupMap X₀) :=
      (Nat.bijective_iff_surjective_and_card _).mpr
        ⟨MonoidHom.subgroupMap_surjective φ₁ X₀, by rw [hXcard, hmapcard]⟩
    intro x hx y hy hxy
    have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
    exact congrArg Subtype.val this
  have hCP : C ≤ P := le_sup_right
  have hdec : ∀ k ∈ P.subgroupOf K, ∃ x ∈ X₀, ∃ c ∈ C.subgroupOf K, k = x * c := by
    intro k hk
    have hkP : (k : Q) ∈ P := hk
    have hCN : C ≤ normalizer (X : Set Q) := hCP.trans hPnorm
    have hmul : (k : Q) ∈ (X : Set Q) * (C : Set Q) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X C hCN]
      exact hkP
    obtain ⟨x, hx, c, hc, hxc⟩ := Set.mem_mul.mp hmul
    have hcK : c ∈ K := (inf_le_left : C ≤ K) hc
    exact ⟨⟨x, hXK hx⟩, hx, ⟨c, hcK⟩, hc, Subtype.ext hxc.symm⟩
  have hnorm : ∀ c ∈ C.subgroupOf K, ∀ t ∈ X₀, c * t * c⁻¹ ∈ X₀ := by
    intro c hc t ht
    have hcP : c ∈ P.subgroupOf K := hCP (show (c : Q) ∈ C from hc)
    exact (Subgroup.mem_normalizer_iff.mp (hXP hcP) t).mp ht
  intro x hx hx1 y hy hy1
  have hxK : x ∈ K := hXK hx
  have hyK : y ∈ K := hXK hy
  obtain ⟨c, hc, hcxy⟩ := k4_transitive_of_model φ₁ (X₀ := X₀) (C₀ := C.subgroupOf K)
    (P₀ := P.subgroupOf K) hdec hnorm hCenD hX hinj ⟨x, hxK⟩ hx
    (fun h => hx1 (congrArg Subtype.val h)) ⟨y, hyK⟩ hy (fun h => hy1 (congrArg Subtype.val h))
  exact ⟨(c : Q), hc, congrArg Subtype.val hcxy⟩

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
