module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusOMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusNCoord
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusAbs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusTr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFNorm1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Open CFSG.Quasithin Subgroup

theorem charP_two_of_card_pow {F : Type} [Field F] [Finite F] {k : ℕ}
    (hF : Nat.card F = 2 ^ k) (hk : 1 ≤ k) : CharP F 2 := by
  haveI := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  obtain ⟨m, hpp, hm⟩ := FiniteField.card F p
  have h1 : p ^ (m : ℕ) = 2 ^ k := by
    rw [← hm, ← hF, Nat.card_eq_fintype_card]
  have h2 : p ∣ 2 ^ k := by
    rw [← h1]
    exact dvd_pow_self p (PNat.ne_zero m)
  have h3 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h2)
  subst h3
  exact hp

theorem one_le_of_card_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : 1 ≤ n := by
  by_contra h0
  have hn : n = 0 := by omega
  subst hn
  have h1 : Nat.card F = 1 := by simpa using hF
  have := Finite.one_lt_card (α := F)
  omega

theorem torusStepO : TorusStepO := by
  intro V _ _ hV n L D M₀ M₁ hS hO hcount
  haveI : IsF2Space V := ⟨hV⟩
  obtain ⟨F, hF1, hF2, b, c, hF, hirr, ε', ψ, hψ⟩ := hO
  have hn : 1 ≤ n := one_le_of_card_pow hF
  haveI : CharP F 2 := charP_two_of_card_pow hF hn
  obtain ⟨M⟩ := nonempty_normModel hirr hF hn
  have hE : Nat.card M.E = (2 ^ n) ^ 2 := by rw [M.card_E, hF]
  haveI : CharP M.E 2 := torusN_charP_two_of_card hn hE
  letI : Algebra (ZMod 2) M.E := ZMod.algebra _ _
  have hqodd : Odd (Nat.card F + 1) := by
    rw [hF]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
  obtain ⟨ω, hω, hω1, hdeg⟩ := exists_primitive_normOne hn hE
  have hω' : ω ^ (Nat.card F + 1) = 1 := by rw [hF]; exact hω
  haveI : Module.Finite (ZMod 2) M.E := Module.Finite.of_finite
  have hint : IsIntegral (ZMod 2) ω := IsIntegral.of_finite (ZMod 2) ω
  have hm : Irreducible (minpoly (ZMod 2) ω) := minpoly.irreducible hint
  have hd : 2 ≤ (minpoly (ZMod 2) ω).natDegree := by rw [hdeg]; omega
  let ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
    (secIso hS.simple hS.le hS.inv hS.stab₀ hS.nc).trans ε'
  have hεψ : ∀ (g : MulAut V) (hg : g ∈ L) (s : Sec M₁ M₀),
      ψ (secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s) = Multiplicative.ofAdd
        (((ε ⟨g, hg⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            F).mulVec (Multiplicative.toAdd (ψ s))) := by
    intro g hg s
    have := hψ (secIso hS.simple hS.le hS.inv hS.stab₀ hS.nc ⟨g, hg⟩) s
    rw [secIso_apply] at this
    exact this
  let ψ' : Sec M₁ M₀ ≃* Multiplicative (Fin 3 → M.E) :=
    ψ.trans M.T.toAddEquiv.toMultiplicative
  have hψ' : ∀ s : Sec M₁ M₀, Multiplicative.toAdd (ψ' s) = M.T (Multiplicative.toAdd (ψ s)) :=
    fun s => rfl
  obtain ⟨a₀, ha₀1, ha₀⟩ := exists_mem_torusO_head M hω' hω1
  obtain ⟨P, π, hπ, hP⟩ := exists_permO M
  have hconj' : ∀ a : Fin 3 → ↥(NormOne M), ∃ e : Fin 3 → ↥(NormOne M),
      (∀ i, e i = a (π i)) ∧ P⁻¹ * torusO M a * P = torusO M e := by
    intro a
    obtain ⟨d, h1, h3⟩ := hP (fun i => a (π i))
    have hda : d = a := by
      funext j
      have := h1 (π.symm j)
      simpa using this
    subst hda
    refine ⟨fun i => d (π i), fun i => rfl, ?_⟩
    rw [← h3]
    group
  have hTD : IsTorusDataIn 3 (torusO M).range
      (fun j => (kerEval M j).map (torusO M)) P (torusO M a₀) π := by
    refine isTorusDataIn_of_hom (torusO M) (torusO_injective M) hqodd (normOne_pow M)
      (kerEval M) (fun i j hij => kerEval_sup M hij) P π hπ
      (fun a => (hP a).imp fun a' h => h.2) (fun a => (hconj' a).imp fun a' h => h.2) ?_ ?_
      a₀ ha₀1
    · intro i a ha
      obtain ⟨a', h1, h3⟩ := hP a
      refine ⟨a', ?_, h3⟩
      rw [mem_kerEval] at ha ⊢
      rw [h1 i]
      exact ha
    · intro i a ha
      obtain ⟨a', h1, h3⟩ := hconj' a
      refine ⟨a', ?_, h3⟩
      rw [mem_kerEval] at ha ⊢
      rw [h1 i]
      exact ha
  have hT := hTD.isTorusData ε
  let W : Fin 3 → Subgroup (Sec M₁ M₀) := fun i => (coordSub M.E i).comap ψ'.toMonoidHom
  have hWind : iSupIndep W :=
    iSupIndep_comap_mulEquiv ψ' (fun i => coordSub M.E i) iSupIndep_coordSub
  have hWtop : ⨆ i, W i = ⊤ := iSup_comap_mulEquiv ψ' _ iSup_coordSub
  have hmemW : ∀ i s, s ∈ W i ↔ ∀ j, j ≠ i → Multiplicative.toAdd (ψ' s) j = 0 :=
    fun i s => Iff.rfl
  have hact : ∀ (g : MulAut V) (hg : g ∈ L) (a : Fin 3 → ↥(NormOne M)),
      ε ⟨g, hg⟩ = torusO M a → ∀ (s : Sec M₁ M₀) (i : Fin 3),
      Multiplicative.toAdd (ψ' (secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s)) i =
        ((((a i : ↥(NormOne M)) : M.Eˣ)) : M.E) * Multiplicative.toAdd (ψ' s) i := by
    intro g hg a hb s i
    rw [hψ', hεψ g hg s, hb, toAdd_ofAdd, torusO_apply]
    rfl
  have hWstab : ∀ i, ∀ g (hg : g ∈ L), g ∈ pbSub ε (torusO M).range → ∀ s ∈ W i,
      secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s ∈ W i := by
    intro i g hg hgΘ s hs
    obtain ⟨hg', a, hb⟩ := (mem_pbSub ε _).mp hgΘ
    rw [hmemW]
    intro j hj
    rw [hact g hg a hb.symm, (hmemW i s).mp hs j hj, mul_zero]
  have hWfix : ∀ j, ∀ s : Sec M₁ M₀, (∀ g (hg : g ∈ L),
      g ∈ pbSub ε ((kerEval M j).map (torusO M)) →
        secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s = s) → s ∈ W j := by
    intro j s hs
    rw [hmemW]
    intro k hk
    have hω0 : ω ≠ 0 := by
      rintro rfl
      simp at hω'
    let ω₀ : ↥(NormOne M) := ⟨Units.mk0 ω hω0, by
      rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using hω')⟩
    let a : Fin 3 → ↥(NormOne M) := Pi.mulSingle k ω₀
    have haj : a ∈ kerEval M j := by
      rw [mem_kerEval]
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(NormOne M)) (Ne.symm hk) ω₀
    have hgmem : pbElt ε (torusO M a) ∈ pbSub ε ((kerEval M j).map (torusO M)) :=
      pbElt_mem_pbSub ε ⟨a, haj, rfl⟩
    have h1 := hs _ (pbElt_mem ε _) hgmem
    have h3 := congrArg (fun t => Multiplicative.toAdd (ψ' t) k) h1
    rw [hact _ (pbElt_mem ε _) a (by simp [pbElt])] at h3
    have hak : ((((a k : ↥(NormOne M)) : M.Eˣ)) : M.E) = ω := by
      simp [a, ω₀]
    rw [hak] at h3
    have h4 : (ω - 1) * Multiplicative.toAdd (ψ' s) k = 0 := by
      rw [sub_mul, h3, one_mul, sub_self]
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hω1)
  have hWtriv : ∀ j, ∀ g (hg : g ∈ L),
      g ∈ pbSub ε ((kerEval M j).map (torusO M)) → ∀ s ∈ W j,
        secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s = s := by
    intro j g hg hgΘ s hs
    obtain ⟨hg', a, ha, hbg⟩ := (mem_pbSub ε _).mp hgΘ
    have haj : a j = 1 := ha
    apply ψ'.injective
    apply Multiplicative.toAdd.injective
    funext i
    rw [hact g hg a hbg.symm]
    by_cases hij : i = j
    · subst hij
      rw [haj]
      simp
    · rw [(hmemW j s).mp hs i hij, mul_zero]
  have hWkill : ∀ s ∈ W 0, polyAct (secAct L hS.inv hS.stab₀
      ⟨pbElt ε (torusO M a₀), hT.le_L hT.θ₀_mem⟩) (minpoly (ZMod 2) ω) s = 1 := by
    intro s hs
    have hθ₀L : pbElt ε (torusO M a₀) ∈ L := pbElt_mem ε _
    have hεθ₀ : ε ⟨pbElt ε (torusO M a₀), hθ₀L⟩ = torusO M a₀ := by
      simp [pbElt]
    let u : Fin 3 → M.Eˣ := fun i => ((a₀ i : ↥(NormOne M)) : M.Eˣ)
    have hf : ∀ t, ψ' (secAct L hS.inv hS.stab₀
        ⟨pbElt ε (torusO M a₀), hT.le_L hT.θ₀_mem⟩ t) = scaleAut u (ψ' t) := by
      intro t
      apply Multiplicative.toAdd.injective
      funext i
      rw [hact _ hθ₀L a₀ hεθ₀ t i]
      rfl
    have key := polyAct_map ψ'.toMonoidHom hf (minpoly (ZMod 2) ω) s
    have hone : polyAct (scaleAut u) (minpoly (ZMod 2) ω) (ψ' s) = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [polyAct_scaleAut]
      by_cases hi : i = 0
      · subst hi
        have hu0 : ((u 0 : M.Eˣ) : M.E) = ω := ha₀
        rw [hu0, minpoly.aeval, zero_mul]
        rfl
      · rw [(hmemW 0 s).mp hs i hi, mul_zero]
        rfl
    apply ψ'.injective
    rw [map_one]
    exact key.trans hone
  have hWcard : Nat.card ↥(W 0) ≤ 2 ^ (minpoly (ZMod 2) ω).natDegree := by
    have h1 : Nat.card ↥(W 0) ≤ Nat.card M.E := by
      refine Nat.card_le_card_of_injective
        (fun s : ↥(W 0) => Multiplicative.toAdd (ψ' s.1) 0) ?_
      intro s s' h
      apply Subtype.ext
      apply ψ'.injective
      apply Multiplicative.toAdd.injective
      funext i
      by_cases hi : i = 0
      · subst hi
        exact h
      · rw [(hmemW 0 s.1).mp s.2 i hi, (hmemW 0 s'.1).mp s'.2 i hi]
    rw [hdeg, ← pow_mul, mul_comm 2 n] at *
    rw [hE] at h1
    exact h1
  exact torusStep_of_secData hS hT (by norm_num) (0 : Fin 3) hm hd W hWind hWtop hWstab hWfix
    hWtriv hWkill hWcard (e := 2) le_rfl hcount

end CFSG.LocalAnalysis.RankThreeUC
