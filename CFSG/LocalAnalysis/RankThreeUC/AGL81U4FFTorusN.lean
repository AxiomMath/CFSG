module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusNMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusNCoord
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusAbs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusTr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFNorm1

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Open CFSG.Quasithin Subgroup

theorem torusT_comp_perm {F : Type} [Field F] {q : ℕ} (σ : Equiv.Perm (Fin 4))
    {a : Fin 4 → Fˣ} (ha : a ∈ torusT F q) : a ∘ σ ∈ torusT F q := by
  refine ⟨fun i => ha.1 (σ i), ?_⟩
  have : ∏ i, (a ∘ σ) i = ∏ i, a i := Equiv.prod_comp σ a
  rw [this]
  exact ha.2

theorem isTorusDataIn_N {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 1 ≤ q)
    (hqodd : Odd (q + 1)) (h2 : (2 : F) = 0) {ω : F} (hω : ω ^ (q + 1) = 1) (hω1 : ω ≠ 1) :
    ∃ (P : ↥(StatedSU 4 q F)) (σ : Equiv.Perm (Fin 4)) (a₀ : ↥(torusT F q)),
      (((a₀ : Fin 4 → Fˣ) 0 : Fˣ) : F) = ω ∧
      IsTorusDataIn 4 (torusDiagSU q hq).range
        (fun j => ((torusTi F q j).subgroupOf (torusT F q)).map (torusDiagSU q hq))
        P (torusDiagSU q hq a₀) σ := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  obtain ⟨P, σ, hσ, hP⟩ := exists_permSU hq h2
  obtain ⟨a₀', ha₀'T, ha₀'⟩ := exists_mem_torusT_head hω hω0
  have hconj : ∀ a : ↥(torusT F q), ∃ a' : ↥(torusT F q),
      (∀ i, (a' : Fin 4 → Fˣ) (σ i) = (a : Fin 4 → Fˣ) i) ∧
        P * torusDiagSU q hq a * P⁻¹ = torusDiagSU q hq a' := hP
  have hconj' : ∀ a : ↥(torusT F q), ∃ b : ↥(torusT F q),
      (∀ i, (b : Fin 4 → Fˣ) i = (a : Fin 4 → Fˣ) (σ i)) ∧
        P⁻¹ * torusDiagSU q hq a * P = torusDiagSU q hq b := by
    intro a
    let c : ↥(torusT F q) := ⟨(a : Fin 4 → Fˣ) ∘ σ, torusT_comp_perm σ a.2⟩
    obtain ⟨d, h1, h3⟩ := hconj c
    have hfun : (d : Fin 4 → Fˣ) = (a : Fin 4 → Fˣ) := by
      funext j
      have := h1 (σ.symm j)
      simpa [c] using this
    have hda : d = a := Subtype.ext hfun
    subst hda
    refine ⟨c, fun i => rfl, ?_⟩
    rw [← h3]
    group
  have ha₀1 : (⟨a₀', ha₀'T⟩ : ↥(torusT F q)) ≠ 1 := by
    intro h
    have h1 : a₀' 0 = 1 := by
      have := congrArg (fun a : ↥(torusT F q) => (a : Fin 4 → Fˣ) 0) h
      simpa using this
    apply hω1
    rw [← ha₀', h1]
    rfl
  refine ⟨P, σ, ⟨a₀', ha₀'T⟩, ha₀', ?_⟩
  refine isTorusDataIn_of_hom (torusDiagSU q hq) (torusDiagSU_injective hq) hqodd
    (fun a => torusT_pow a) (fun j => (torusTi F q j).subgroupOf (torusT F q)) ?_ P σ hσ
    (fun a => (hconj a).imp fun a' h => h.2) (fun a => (hconj' a).imp fun a' h => h.2) ?_ ?_
    ⟨a₀', ha₀'T⟩ ha₀1
  · intro i j hij
    rw [← Subgroup.subgroupOf_sup (torusTi_le q i) (torusTi_le q j), torusTi_sup hij,
      Subgroup.subgroupOf_self]
  · intro i a ha
    obtain ⟨a', h1, h3⟩ := hconj a
    refine ⟨a', ?_, h3⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨a'.2, ?_⟩
    show (a' : Fin 4 → Fˣ) (σ i) = 1
    rw [h1 i]
    exact ha.2
  · intro i a ha
    obtain ⟨a', h1, h3⟩ := hconj' a
    refine ⟨a', ?_, h3⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨a'.2, ?_⟩
    show (a' : Fin 4 → Fˣ) i = 1
    rw [h1 i]
    exact ha.2

theorem one_le_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : 1 ≤ n := by
  by_contra h0
  have hn : n = 0 := by omega
  subst hn
  have h1 : Nat.card F = 1 := by simpa using hF
  have := Finite.one_lt_card (α := F)
  omega

theorem torusStepN : TorusStepN := by
  intro V _ _ hV n L D M₀ M₁ hS hN hcount
  haveI : IsF2Space V := ⟨hV⟩
  obtain ⟨F, hF1, hF2, hF, ε', ψ, hψ⟩ := hN
  have hn : 1 ≤ n := one_le_of_card_sq hF
  haveI : CharP F 2 := torusN_charP_two_of_card hn hF
  letI : Algebra (ZMod 2) F := ZMod.algebra _ _
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hqodd : Odd (2 ^ n + 1) := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨ω, hω, hω1, hdeg⟩ := exists_primitive_normOne hn hF
  haveI : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hint : IsIntegral (ZMod 2) ω := IsIntegral.of_finite (ZMod 2) ω
  have hm : Irreducible (minpoly (ZMod 2) ω) := minpoly.irreducible hint
  have hd : 2 ≤ (minpoly (ZMod 2) ω).natDegree := by rw [hdeg]; omega
  let ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F) :=
    (secIso hS.simple hS.le hS.inv hS.stab₀ hS.nc).trans ε'
  have hεψ : ∀ (g : MulAut V) (hg : g ∈ L) (s : Sec M₁ M₀),
      ψ (secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s) = Multiplicative.ofAdd
        (((ε ⟨g, hg⟩ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
          (Multiplicative.toAdd (ψ s))) := by
    intro g hg s
    have := hψ (secIso hS.simple hS.le hS.inv hS.stab₀ hS.nc ⟨g, hg⟩) s
    rw [secIso_apply] at this
    exact this
  obtain ⟨P, σ, a₀, ha₀, hTD⟩ := isTorusDataIn_N hq hqodd h2 hω hω1
  have hT := hTD.isTorusData ε
  let W : Fin 4 → Subgroup (Sec M₁ M₀) := fun i => (coordSub F i).comap ψ.toMonoidHom
  have hWind : iSupIndep W :=
    iSupIndep_comap_mulEquiv ψ (fun i => coordSub F i) iSupIndep_coordSub
  have hWtop : ⨆ i, W i = ⊤ := iSup_comap_mulEquiv ψ _ iSup_coordSub
  have hmemW : ∀ i s, s ∈ W i ↔ ∀ j, j ≠ i → Multiplicative.toAdd (ψ s) j = 0 :=
    fun i s => Iff.rfl
  have hact : ∀ (g : MulAut V) (hg : g ∈ L) (b : ↥(torusT F (2 ^ n))),
      ε ⟨g, hg⟩ = torusDiagSU (2 ^ n) hq b → ∀ (s : Sec M₁ M₀) (i : Fin 4),
      Multiplicative.toAdd (ψ (secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s)) i =
        (((b : Fin 4 → Fˣ) i : Fˣ) : F) * Multiplicative.toAdd (ψ s) i := by
    intro g hg b hb s i
    rw [hεψ g hg s, hb, torusDiagSU_mulVec]
    rfl
  have hWstab : ∀ i, ∀ g (hg : g ∈ L), g ∈ pbSub ε (torusDiagSU (2 ^ n) hq).range → ∀ s ∈ W i,
      secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s ∈ W i := by
    intro i g hg hgΘ s hs
    obtain ⟨hg', b, hb⟩ := (mem_pbSub ε _).mp hgΘ
    rw [hmemW]
    intro j hj
    rw [hact g hg b hb.symm, (hmemW i s).mp hs j hj, mul_zero]
  have hWfix : ∀ j, ∀ s : Sec M₁ M₀, (∀ g (hg : g ∈ L),
      g ∈ pbSub ε (((torusTi F (2 ^ n) j).subgroupOf (torusT F (2 ^ n))).map
        (torusDiagSU (2 ^ n) hq)) → secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s = s) → s ∈ W j := by
    intro j s hs
    rw [hmemW]
    intro k hk
    obtain ⟨a, haT, hak⟩ := exists_mem_torusTi_apply hω hω1 hk
    let b : ↥(torusT F (2 ^ n)) := ⟨a, haT.1⟩
    have hgmem : pbElt ε (torusDiagSU (2 ^ n) hq b) ∈ pbSub ε (((torusTi F (2 ^ n) j).subgroupOf
        (torusT F (2 ^ n))).map (torusDiagSU (2 ^ n) hq)) :=
      pbElt_mem_pbSub ε ⟨b, haT, rfl⟩
    have h1 := hs _ (pbElt_mem ε _) hgmem
    have h3 := congrArg (fun t => Multiplicative.toAdd (ψ t) k) h1
    rw [hact _ (pbElt_mem ε _) b (by simp [pbElt]), hak] at h3
    have h4 : (ω - 1) * Multiplicative.toAdd (ψ s) k = 0 := by
      rw [sub_mul, h3, one_mul, sub_self]
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hω1)
  have hWtriv : ∀ j, ∀ g (hg : g ∈ L),
      g ∈ pbSub ε (((torusTi F (2 ^ n) j).subgroupOf (torusT F (2 ^ n))).map
        (torusDiagSU (2 ^ n) hq)) → ∀ s ∈ W j, secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s = s := by
    intro j g hg hgΘ s hs
    obtain ⟨hg', b, hb, hbg⟩ := (mem_pbSub ε _).mp hgΘ
    have hbj : ((b : Fin 4 → Fˣ) j) = 1 := (Subgroup.mem_subgroupOf.mp hb).2
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    funext i
    rw [hact g hg b hbg.symm]
    by_cases hij : i = j
    · subst hij
      rw [hbj]
      simp
    · rw [(hmemW j s).mp hs i hij, mul_zero]
  have hWkill : ∀ s ∈ W 0, polyAct (secAct L hS.inv hS.stab₀
      ⟨pbElt ε (torusDiagSU (2 ^ n) hq a₀), hT.le_L hT.θ₀_mem⟩) (minpoly (ZMod 2) ω) s = 1 := by
    intro s hs
    have hθ₀L : pbElt ε (torusDiagSU (2 ^ n) hq a₀) ∈ L := pbElt_mem ε _
    have hεθ₀ : ε ⟨pbElt ε (torusDiagSU (2 ^ n) hq a₀), hθ₀L⟩ = torusDiagSU (2 ^ n) hq a₀ := by
      simp [pbElt]
    have hf : ∀ t, ψ (secAct L hS.inv hS.stab₀
        ⟨pbElt ε (torusDiagSU (2 ^ n) hq a₀), hT.le_L hT.θ₀_mem⟩ t) =
        scaleAut (a₀ : Fin 4 → Fˣ) (ψ t) := by
      intro t
      apply Multiplicative.toAdd.injective
      funext i
      rw [hact _ hθ₀L a₀ hεθ₀ t i]
      rfl
    have key := polyAct_map ψ.toMonoidHom hf (minpoly (ZMod 2) ω) s
    have hone : polyAct (scaleAut (a₀ : Fin 4 → Fˣ)) (minpoly (ZMod 2) ω) (ψ s) = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [polyAct_scaleAut]
      by_cases hi : i = 0
      · subst hi
        rw [ha₀, minpoly.aeval, zero_mul]
        rfl
      · rw [(hmemW 0 s).mp hs i hi, mul_zero]
        rfl
    apply ψ.injective
    rw [map_one]
    exact key.trans hone
  have hWcard : Nat.card ↥(W 0) ≤ 2 ^ (minpoly (ZMod 2) ω).natDegree := by
    have h1 : Nat.card ↥(W 0) ≤ Nat.card F := by
      refine Nat.card_le_card_of_injective
        (fun s : ↥(W 0) => Multiplicative.toAdd (ψ s.1) 0) ?_
      intro s s' h
      apply Subtype.ext
      apply ψ.injective
      apply Multiplicative.toAdd.injective
      funext i
      by_cases hi : i = 0
      · subst hi
        exact h
      · rw [(hmemW 0 s.1).mp s.2 i hi, (hmemW 0 s'.1).mp s'.2 i hi]
    rw [hdeg, hF, ← pow_mul, mul_comm n 2] at *
    exact h1
  have hcount' : Nat.card (commV L) ≤
      1 * Nat.card (autSub D (commV L)) * Nat.card ↥(commV L ⊓ fixV D) := by
    simpa using hcount
  exact torusStep_of_secData hS hT (by norm_num) (0 : Fin 4) hm hd W hWind hWtop hWstab hWfix
    hWtriv hWkill hWcard (e := 1) (by norm_num) hcount'

end CFSG.LocalAnalysis.RankThreeUC
