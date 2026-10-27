module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatBS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPrime
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

section Normal2

variable {H : Type*} [Group H] {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem eq_bot_of_normal_isPGroup (A : Subgroup (Gamma k)) (hA : IsPGroup 2 A)
    (hN : ∀ g ∈ slGamma k, ∀ a ∈ A, g * a * g⁻¹ ∈ A) : A = ⊥ := by
  classical
  obtain ⟨w, hw0, hw⟩ := exists_fixed_vec_of_isPGroup (A.map (Gamma k).subtype)
    (by rintro _ ⟨a, -, rfl⟩; exact a.2) (hA.map (Gamma k).subtype)
  have hw' : ∀ a ∈ A, (a : Equiv.Perm (Fin 2 → k)) w = w := fun a ha => hw _ ⟨a, ha, rfl⟩
  have hall : ∀ u : Fin 2 → k, u ≠ 0 → ∀ a ∈ A, (a : Equiv.Perm (Fin 2 → k)) u = u := by
    intro u hu a ha
    obtain ⟨g1, hg1⟩ := exists_smul_e0 hw0
    obtain ⟨g2, hg2⟩ := exists_smul_e0 hu
    set B : Matrix.SpecialLinearGroup (Fin 2) k := g2 * g1⁻¹ with hB
    have hBw : slPerm k B w = u := by
      rw [slPerm_apply, hB, mul_smul, ← hg1, inv_smul_smul, hg2]
    set gB : Gamma k := ⟨slPerm k B, slPerm_mem_Gamma B⟩ with hgBdef
    have hgB : gB ∈ slGamma k := slPerm_mem_slGamma B
    have h2 : gB⁻¹ * a * gB ∈ A := by
      have := hN gB⁻¹ (inv_mem hgB) a ha
      simpa using this
    have h3 := hw' _ h2
    have h4 : ((a : Equiv.Perm (Fin 2 → k)) * (gB : Equiv.Perm (Fin 2 → k))) w =
        ((gB : Equiv.Perm (Fin 2 → k)) * ((gB⁻¹ * a * gB : Gamma k) : Equiv.Perm (Fin 2 → k))) w := by
      congr 1
      simp [mul_assoc]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h3] at h4
    have hgw : (gB : Equiv.Perm (Fin 2 → k)) w = u := hBw
    rw [hgw] at h4
    exact h4
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  apply Subtype.ext
  refine Equiv.ext fun u => ?_
  by_cases hu : u = 0
  · subst hu
    rw [Gamma_apply_zero a.2]
    rfl
  · exact hall u hu a ha

theorem le_ker_of_normal_isPGroup {ρ : H →* Gamma k} {H₀ N : Subgroup H}
    (hρ : H₀.map ρ = slGamma k) (hNn : H₀ ≤ Subgroup.normalizer (N : Set H))
    (hN2 : IsPGroup 2 N) : N ≤ ρ.ker := by
  have hA := eq_bot_of_normal_isPGroup (N.map ρ) (hN2.map ρ) (by
    intro g hg a ha
    rw [← hρ] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    obtain ⟨n, hn, rfl⟩ := ha
    refine ⟨x * n * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNn hx) n).mp hn)
  intro n hn
  have : ρ n ∈ N.map ρ := ⟨n, hn, rfl⟩
  rw [hA, Subgroup.mem_bot] at this
  exact this

theorem frattini_slGamma_eq_bot : frattini (slGamma k) = ⊥ := by
  have h := frattini_map_equiv (slGammaEquiv k)
  rw [frattini_specialLinear_two_eq_bot k, Subgroup.map_bot] at h
  exact h.symm

end Normal2

section Overgroup

variable {H : Type*} [Group H]

@[expose] def NoCharNormal (S P : Subgroup H) : Prop :=
  ∀ C : Subgroup H, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
    ¬ P ≤ Subgroup.normalizer (C : Set H)

@[expose] def baumannOvergroup (R : Subgroup H) : Subgroup H :=
  oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R

theorem characteristic_elemBaumannIn [Finite H] (R : Subgroup H) :
    ((elemBaumannIn 2 R).subgroupOf R).Characteristic := by
  have h : elemBaumannIn 2 R = baum R := elemBaumann_map_subtype_eq_baum R
  rw [h]
  exact CFSG.Quasithin.C1GN.characteristic_baum R

theorem NoCharNormal.of_sup_eq_top {R S H₀ : Subgroup H} (hSR : S ≤ R)
    (hS : (S.subgroupOf R).Characteristic) (hsup : H₀ ⊔ R = ⊤) (h : NoCharNormal R ⊤) :
    NoCharNormal S H₀ := by
  intro C hCS hC0 hCchar hN
  have hCR : C ≤ R := hCS.trans hSR
  have hchR : (C.subgroupOf R).Characteristic :=
    CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans hSR hCS hS hCchar
  have key : ∀ r ∈ R, ∀ x ∈ C, r * x * r⁻¹ ∈ C := by
    intro r hr x hx
    have h1 := Subgroup.characteristic_iff_map_eq.mp hchR (MulAut.conj (⟨r, hr⟩ : R))
    have h2 : (MulAut.conj (⟨r, hr⟩ : R)) ⟨x, hCR hx⟩ ∈
        (C.subgroupOf R).map (MulAut.conj (⟨r, hr⟩ : R)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hRN : R ≤ Subgroup.normalizer (C : Set H) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key r hr x, fun hx => by simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hx⟩
  refine h C hCR hC0 hchR ?_
  rw [← hsup]
  exact sup_le hN hRN

end Overgroup

section Main

variable {H : Type*} [Group H] [Finite H] {k : Type*} [Field k] [Finite k] [CharP k 2]

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem Baumann_Stellmacher_hypotheses (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowTwoOf (elemBaumannIn 2 R) (baumannOvergroup R) ∧
      (baumannOvergroup R).IsSubnormal ∧
      CharTwo (baumannOvergroup R) ∧
      baumannOvergroup R ⊔ R = ⊤ ∧
      (CFSG.pCore 2 (baumannOvergroup R)).map (baumannOvergroup R).subtype =
        CFSG.pCore 2 H ⊓ baumannOvergroup R ∧
      CFSG.pCore 2 H ⊓ baumannOvergroup R = CFSG.pCore 2 H ⊓ elemBaumannIn 2 R ∧
      (ρ.ker.subgroupOf (baumannOvergroup R)).map
          (QuotientGroup.mk' (CFSG.pCore 2 (baumannOvergroup R))) =
        frattini (baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R)) ∧
      (∃ e : ((baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R)) ⧸
            frattini (baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R))) ≃*
          Matrix.SpecialLinearGroup (Fin 2) k,
        ∀ x : baumannOvergroup R,
          slPerm k (e (QuotientGroup.mk (QuotientGroup.mk x))) =
            ((ρ (x : H) : Gamma k) : Equiv.Perm (Fin 2 → k))) ∧
      ¬ IsElemAbelian 2 (elemBaumannIn 2 R) ∧
      NoCharNormal (elemBaumannIn 2 R) (baumannOvergroup R) := by
  classical
  have hVH := h.not_le_centralizer hJ
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  obtain ⟨hHLR, -, -, -, -, hfr, -⟩ :=
    minimal_parabolic_reduced_module_Frattini_kernel_production h.sylow h.nonnormal h.le_M h.M_lt
      h.M_max h.reduced hVH
  obtain ⟨ℓ, hsyl, -, -, -, hρH₀, -⟩ := h.Baumann_Sylow hJ
  have hRQ : R ⊓ ρ.ker = CFSG.pCore 2 H := h.inf_ker_eq hVH
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set S : Subgroup H := elemBaumannIn 2 R with hSdef
  set Q : Subgroup H := CFSG.pCore 2 H with hQdef
  set H₀ : Subgroup H := baumannOvergroup R with hH₀def
  have hρH₀' : H₀.map ρ = slGamma k := hρH₀
  have hSR : S ≤ R := elemBaumannIn_le 2 R
  have hLH₀ : L ≤ H₀ := le_sup_left
  have hSH₀ : S ≤ H₀ := le_sup_right
  have hQker : Q ≤ ρ.ker := fun x hx => (hRQ ▸ hx : x ∈ R ⊓ ρ.ker).2
  have hL2 : ∀ x : H ⧸ L, ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    intro x
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := h') trivial
    exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hn⟩
  have h1 : IsSylowTwoOf S H₀ := hsyl
  have h2 : H₀.IsSubnormal := isSubnormal_of_pGroup_quotient L (hL2 : IsPGroup 2 (H ⧸ L)) hLH₀
  have h3 : CharTwo H₀ := hchar.of_isSubnormal le_top h2.subgroupOf
  have h4 : H₀ ⊔ R = ⊤ := by
    have : L ⊔ R ≤ H₀ ⊔ R := sup_le_sup_right hLH₀ R
    rw [hHLR] at this
    exact top_le_iff.mp this
  have hQ₀le : CFSG.Open.pCoreOf 2 H₀ ≤ ρ.ker :=
    le_ker_of_normal_isPGroup hρH₀'
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H₀)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H₀)
  have hQ₀S : CFSG.Open.pCoreOf 2 H₀ ≤ S := h1.pCoreOf_le
  have hSker : S ⊓ ρ.ker ≤ Q := fun x hx => hRQ ▸ (⟨hSR hx.1, hx.2⟩ : x ∈ R ⊓ ρ.ker)
  have hQ₀Q : CFSG.Open.pCoreOf 2 H₀ ≤ Q := fun x hx => hSker ⟨hQ₀S hx, hQ₀le hx⟩
  have hQH₀ : Q ⊓ H₀ ≤ CFSG.Open.pCoreOf 2 H₀ := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (Q ⊓ H₀) H₀
      inf_le_right ?_ ((CFSG.pCore_isPGroup (p := 2) (G := H)).to_le inf_le_left)
    refine (BlueprintB2.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxH⟩
      exact ⟨hQn.conj_mem x hxQ g, H₀.mul_mem (H₀.mul_mem hg hxH) (H₀.inv_mem hg)⟩
    · rintro ⟨hxQ, hxH⟩
      refine ⟨by simpa [mul_assoc] using hQn.conj_mem _ hxQ g⁻¹, ?_⟩
      simpa [mul_assoc] using H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hg) hxH) hg
  have hQ₀eq : CFSG.Open.pCoreOf 2 H₀ = Q ⊓ H₀ :=
    le_antisymm (le_inf hQ₀Q (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H₀)) hQH₀
  have hQSeq : Q ⊓ H₀ = Q ⊓ S :=
    le_antisymm (le_inf inf_le_left (hQH₀.trans hQ₀S)) (inf_le_inf_left Q hSH₀)
  have hQ₀map : (CFSG.pCore 2 ↥H₀).map H₀.subtype = Q ⊓ H₀ := by
    rw [← pCoreOf_eq 2 H₀]; exact hQ₀eq
  have hSne : S ≠ ⊥ := by
    intro hS0
    apply hJ
    have hJS : elemThompsonIn 2 R ≤ S := elemThompsonIn_le_elemBaumannIn 2 R
    have hJ0 : elemThompsonIn 2 R = ⊥ := le_bot_iff.mp (hS0 ▸ hJS)
    rw [hJ0]
    exact Subgroup.commutator_bot_left _
  have hS_char : (S.subgroupOf R).Characteristic := characteristic_elemBaumannIn R
  have h10 : NoCharNormal S H₀ := NoCharNormal.of_sup_eq_top hSR hS_char h4 hnc
  have h9 : ¬ IsElemAbelian 2 S := by
    intro hE
    have hSc : IsMulCommutative S := hE.1
    have hcomm : S ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H₀ : Set H) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := S)).comm ⟨y, hQ₀S hy⟩ ⟨x, hx⟩)
    have hSQ₀ : S ≤ CFSG.Open.pCoreOf 2 H₀ := fun x hx => h3 ⟨hSH₀ hx, hcomm hx⟩
    have hSeq : CFSG.Open.pCoreOf 2 H₀ = S := le_antisymm hQ₀S hSQ₀
    have hnorm : H₀ ≤ Subgroup.normalizer (S : Set H) := by
      rw [← hSeq]
      exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H₀
    exact h10 S le_rfl hSne (by rw [Subgroup.subgroupOf_self]; infer_instance) hnorm
  have hmem₀ : ∀ x : H₀, ρ (x : H) ∈ slGamma k := fun x =>
    hρH₀' ▸ Subgroup.mem_map_of_mem ρ x.2
  let ρ₀ : H₀ →* slGamma k := (ρ.comp H₀.subtype).codRestrict (slGamma k) hmem₀
  have hρ₀ : ∀ x : H₀, ((ρ₀ x : slGamma k) : Gamma k) = ρ (x : H) := fun x => rfl
  have hρ₀surj : Function.Surjective ρ₀ := by
    intro g
    have hg : (g : Gamma k) ∈ H₀.map ρ := by
      rw [hρH₀']
      exact g.2
    obtain ⟨x, hx, hxg⟩ := hg
    exact ⟨⟨x, hx⟩, Subtype.ext hxg⟩
  have hker₀ : ρ₀.ker = ρ.ker.subgroupOf H₀ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact congrArg (fun y : slGamma k => (y : Gamma k)) hx
    · intro hx
      exact Subtype.ext hx
  have hLp₀ : IsPGroup 2 (H₀ ⧸ L.subgroupOf H₀) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := (y : H)) trivial
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hn)
  have hQ₁ : ∀ x : H₀, x ∈ CFSG.pCore 2 ↥H₀ ↔ (x : H) ∈ Q := by
    intro x
    have hiff : (x : H) ∈ (CFSG.pCore 2 ↥H₀).map H₀.subtype ↔ (x : H) ∈ Q ⊓ H₀ := by
      rw [hQ₀map]
    constructor
    · intro hx
      exact (hiff.mp ⟨x, hx, rfl⟩).1
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hiff.mpr ⟨hx, x.2⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
  have hQD : CFSG.pCore 2 ↥H₀ ≤ ρ₀.ker := by
    intro x hx
    rw [hker₀, Subgroup.mem_subgroupOf]
    exact hQker ((hQ₁ x).mp hx)
  have hNfr : ρ.ker.map (QuotientGroup.mk' Q) ≤ frattini (H ⧸ Q) := by
    rw [← hfr]
    exact Subgroup.map_mono h.ker_le_kerIn
  have hfrSub := frattini_image_in_odd_residual_quotient_sub L H₀ hLH₀ hL2 hNfr
    (CFSG.pCore 2 ↥H₀) hQ₁
  have hnormK : ((H₀ ⊓ ρ.ker).subgroupOf H₀).Normal := by
    have hK : (H₀ ⊓ ρ.ker).subgroupOf H₀ = ρ₀.ker := by
      rw [hker₀]
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hK]
    infer_instance
  have h1' : IsSylowIn 2 S H₀ := h1
  have hSylInf : IsSylowIn 2 (S ⊓ (H₀ ⊓ ρ.ker)) (H₀ ⊓ ρ.ker) :=
    h1'.inf_normal inf_le_left hnormK
  have hSylEq : S ⊓ (H₀ ⊓ ρ.ker) = Q ⊓ H₀ := by
    ext x
    constructor
    · rintro ⟨hxS, -, hxk⟩
      exact ⟨hSker ⟨hxS, hxk⟩, hSH₀ hxS⟩
    · rintro ⟨hxQ, hxH⟩
      have hxS : x ∈ S := (hQSeq ▸ (⟨hxQ, hxH⟩ : x ∈ Q ⊓ H₀) : x ∈ Q ⊓ S).2
      exact ⟨hxS, hxH, hQker hxQ⟩
  rw [hSylEq] at hSylInf
  have hQsyl : ¬ 2 ∣ ((CFSG.pCore 2 ↥H₀).subgroupOf ρ₀.ker).index := by
    have hmapker : ρ₀.ker.map H₀.subtype = H₀ ⊓ ρ.ker := by
      rw [hker₀]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, Subgroup.mem_subgroupOf.mp hy⟩
      · rintro ⟨hxH, hxk⟩
        exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxk, rfl⟩
    have := hSylInf.not_dvd_relIndex
    rw [← hQ₀map, ← hmapker,
      Subgroup.relIndex_map_map_of_injective _ _ H₀.subtype_injective] at this
    exact this
  obtain ⟨hfrat, e, he⟩ := action_kernel_is_frattini (p := 2) ρ₀ hρ₀surj (L.subgroupOf H₀)
    (CFSG.pCore 2 ↥H₀) hLp₀ hQD hQsyl (by rw [hker₀]; exact hfrSub) frattini_slGamma_eq_bot
  refine ⟨h1, h2, h3, h4, hQ₀map, hQSeq, ?_, ?_, h9, h10⟩
  · rw [← hker₀]
    exact hfrat
  · refine ⟨e.trans (slGammaEquiv k).symm, fun x => ?_⟩
    have hx := he x
    show slPerm k ((slGammaEquiv k).symm (e (QuotientGroup.mk (QuotientGroup.mk x)))) = _
    rw [hx]
    have hh := (slGammaEquiv k).apply_symm_apply (ρ₀ x)
    have := congrArg (fun y : slGamma k => ((y : Gamma k) : Equiv.Perm (Fin 2 → k))) hh
    rw [← slGammaEquiv_apply]
    exact this

end IsNatQuotSetting

end Main

end CFSG.QuasithinUnique.Setup.Campbell
