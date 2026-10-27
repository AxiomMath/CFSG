module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBaumannSetup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Pair

public section

set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem mem_twoResidual_of_odd {H : Subgroup G} {x : G} (hx : x ∈ H) (hodd : Odd (orderOf x)) :
    x ∈ twoResidual H := by
  unfold twoResidual
  rw [Subgroup.mem_iInf]
  intro N
  rw [Subgroup.mem_iInf]
  rintro ⟨hNH, hHN, hq⟩
  obtain ⟨k, hk⟩ := hq x hx
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.mp h1]; exact N.one_mem
  have hlt : 1 < orderOf x := by
    have := orderOf_pos x; omega
  obtain ⟨j, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
  have e : x ^ (2 ^ k * j) = x := by rw [← pow_mod_orderOf, hj.2, pow_one]
  have : x = (x ^ 2 ^ k) ^ j := by rw [← pow_mul, e]
  rw [this]
  exact N.pow_mem hk j

theorem exists_pow_two_odd (h : G) : ∃ a : ℕ, Odd (orderOf (h ^ 2 ^ a)) := by
  set a := (orderOf h).factorization 2 with ha
  refine ⟨a, ?_⟩
  have hmodd : Odd (orderOf h / 2 ^ a) := by
    have : ¬ 2 ∣ orderOf h / 2 ^ a := Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos h).ne'
    exact Nat.odd_iff.mpr (by omega)
  have : orderOf (h ^ 2 ^ a) = orderOf h / 2 ^ a := by
    rw [orderOf_pow' _ (by positivity)]
    have hg : Nat.gcd (orderOf h) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (Nat.ordProj_dvd _ _)
    rw [hg]
  rw [this]; exact hmodd

omit [Finite G] in
theorem not_isLin2Type_of_solvable {Y : Subgroup G} (hY : Group.IsSolvable ↥Y) {n : ℕ} (hn : 1 < n) :
    ¬ IsLin2Type Y n := by
  rintro ⟨F, hF, hFin, hcard, α, hsurj, -⟩
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq this
    exact ⟨s, hs⟩
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective hsurj
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := by
    refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, 1, fun h => ?_⟩⟩
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp at this
  exact Group.IsPerfect.not_isSolvable (Matrix.SpecialLinearGroup (Fin 2) F) hsolv

section Ctx

variable {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} (ctx : FFCtx M T V hU hMN I)
  {L : Subgroup (MulAut (IntMod V hU))} (hL : L ∈ I)
include ctx hL

theorem FFCtx.autI_baum_le_normalizer :
    autI hU (baum T) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) :=
  (ctx.hJM ▸ ctx.hBJ).trans (ctx.iSup_le_normalizer hL)

theorem FFCtx.isPGroup_autI_baum : IsPGroup 2 ↥(autI hU (baum T)) := by
  have hB2 : IsPGroup 2 (baum T) := ctx.hT.2.1.to_le (C1GN.baum_le T)
  exact isPGroup_autI hU hB2

theorem FFCtx.exists_pow_mem_L {z : MulAut (IntMod V hU)} (hz : z ∈ L ⊔ autI hU (baum T)) :
    ∃ m : ℕ, z ^ 2 ^ m ∈ L := by
  have hBN := ctx.autI_baum_le_normalizer hL
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left L (autI hU (baum T)) hBN
  have hz' : z ∈ ((L ⊔ autI hU (baum T) : Subgroup _) : Set _) := hz
  rw [hcoe] at hz'
  obtain ⟨l, hl, b, hb, rfl⟩ := hz'
  have hbN : b ∈ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) := hBN hb
  have hlN : l ∈ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) := Subgroup.le_normalizer hl
  obtain ⟨m, hm⟩ := exists_orderOf_two_pow (ctx.isPGroup_autI_baum hL) hb
  refine ⟨m, pow_mem_of_eq_two_mul (N := L) (x := l * b) (o := b) (c := b⁻¹ * l * b)
    (mul_mem hlN hbN) hbN ?_ (by group) hm⟩
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hbN) l).mp hl
  simpa [mul_assoc] using this

end Ctx

section Ctx2

variable {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} (ctx : FFCtx M T V hU hMN I)
  {L : Subgroup (MulAut (IntMod V hU))} (hL : L ∈ I)
  {H₀ : Subgroup G} (hH₀M : H₀ ≤ M)
  (hLB : autI hU H₀ = L ⊔ autI hU (baum T))
include ctx hL hH₀M hLB

theorem FFCtx.twoResidual_le_preAutM :
    twoResidual H₀ ≤ preAutM hU hMN L := by
  set K := preAutM hU hMN L with hK
  have hLH : L ≤ autI hU H₀ := hLB ▸ le_sup_left
  have hLN : autI hU H₀ ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) :=
    hLB ▸ sup_le Subgroup.le_normalizer (ctx.autI_baum_le_normalizer hL)
  have hN : K ⊓ H₀ ∈ {N : Subgroup G | N ≤ H₀ ∧ H₀ ≤ Subgroup.normalizer (N : Set G) ∧
      ∀ x ∈ H₀, ∃ k : ℕ, x ^ 2 ^ k ∈ N} := by
    refine ⟨inf_le_right, ?_, ?_⟩
    · intro h hh
      have h1 : h ∈ Subgroup.normalizer (K : Set G) := by
        refine le_normalizer_preAutM (Y := H₀) hH₀M (fun g hg φ hφ => ?_) hh
        exact (Subgroup.mem_normalizer_iff.mp (hLN hg) φ).mp hφ
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hh⟩
    · intro x hx
      have hxM : x ∈ M := hH₀M hx
      have hz : actM hU hMN ⟨x, hxM⟩ ∈ L ⊔ autI hU (baum T) := by
        rw [← hLB, actM_eq_convI]
        exact convI_mem_autI hU hx (hMN hxM)
      obtain ⟨m, hm⟩ := ctx.exists_pow_mem_L hL hz
      refine ⟨m, ?_, pow_mem hx _⟩
      have hxm : x ^ 2 ^ m ∈ M := pow_mem hxM _
      show x ^ 2 ^ m ∈ preAutM hU hMN L
      rw [mem_preAutM]
      refine ⟨hxm, ?_⟩
      have : (⟨x ^ 2 ^ m, hxm⟩ : ↥M) = (⟨x, hxM⟩ : ↥M) ^ 2 ^ m := rfl
      rw [this, map_pow]
      exact hm
  unfold twoResidual
  exact (iInf₂_le (K ⊓ H₀) hN).trans inf_le_left

theorem FFCtx.not_twoResidual_le_centralizer :
    ¬ twoResidual H₀ ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card L := by rw [ctx.hcard L hL]; norm_num
  obtain ⟨ℓ, hℓ⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
  have hℓL : (ℓ : MulAut (IntMod V hU)) ∈ autI hU H₀ := hLB ▸ le_sup_left (a := L) ℓ.2
  obtain ⟨g, hg, hgℓ⟩ := (mem_autI hU).1 hℓL
  obtain ⟨a, ha⟩ := exists_pow_two_odd (g : G)
  intro hY
  have hyH : (g : G) ^ 2 ^ a ∈ H₀ := pow_mem hg _
  have hyY := mem_twoResidual_of_odd hyH ha
  have hyC := hY hyY
  have hgn : g ^ 2 ^ a = ⟨(g : G) ^ 2 ^ a, by simpa using pow_mem g.2 (2 ^ a)⟩ := by
    apply Subtype.ext; simp
  have h1 : convI hU (g ^ 2 ^ a) = 1 := by
    rw [convI_eq_one_iff]
    simpa using hyC
  rw [map_pow, hgℓ] at h1
  have hord : orderOf (ℓ : MulAut (IntMod V hU)) = 3 := by rw [Subgroup.orderOf_coe, hℓ]
  have hd : 3 ∣ 2 ^ a := hord ▸ orderOf_dvd_of_pow_eq_one h1
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow hd)
  omega

theorem FFCtx.blockLift (hsolv : Group.IsSolvable ↥H₀)
    (hQN : pCoreOf 2 M ≤ Subgroup.normalizer (twoResidual H₀ : Set G))
    (hblock : IsL2OrA3Block H₀ (twoResidual H₀)) :
    ∃ Y : Subgroup G, Y ≤ M ∧ IsSubnormal Y M ∧ InClassXBlock Y := by
  set Y := twoResidual H₀ with hY
  have hYH : Y ≤ H₀ := twoResidual_le H₀
  have hYM : Y ≤ M := hYH.trans hH₀M
  have hshort : IsShort2 Y := hblock.1.1
  have halt : IsAltType Y 3 := by
    rcases hblock.2 with ⟨n, hn, hlin⟩ | h
    · exfalso
      have hYs : Group.IsSolvable ↥Y :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYH)
          (Subgroup.inclusion_injective hYH)
      exact not_isLin2Type_of_solvable hYs hn hlin
    · exact h
  have B : BLCtx M V Y :=
    ⟨hYM, ctx.V_le_pCoreOf, hMN, fun q hq v hv =>
      (Subgroup.mem_centralizer_iff.mp (ctx.pCoreOf_le_centralizer hq).1 v hv).symm, ctx.hCT, hQN,
      hshort, halt, ctx.not_twoResidual_le_centralizer hL hH₀M hLB⟩
  refine ⟨Y, hYM, ?_, hshort, Or.inr ⟨1, le_rfl, halt⟩⟩
  have hLH : L ≤ autI hU H₀ := hLB ▸ le_sup_left
  set K := preAutM hU hMN L with hK
  set C' := Subgroup.centralizer (V : Set G) ⊓ M with hC'
  set S := Y ⊔ C' with hS
  have hCM : M ≤ Subgroup.normalizer (C' : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_centralizer hMN hm,
      Subgroup.le_normalizer hm⟩
  have hYK : Y ≤ K := ctx.twoResidual_le_preAutM hL hH₀M hLB
  have hCK : C' ≤ K := centralizer_inf_le_preAutM hU hMN L
  have hSK : S ≤ K := sup_le hYK hCK
  have hKM : K ≤ M := preAutM_le hU hMN L
  have hkey : ∀ g ∈ K, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro g hg
    obtain ⟨hgM, hgL⟩ := (mem_preAutM hU hMN).1 hg
    have hYS : ∀ x ∈ Y, g * x * g⁻¹ ∈ S := by
      intro x hx
      obtain ⟨g', hg'H, hg'e⟩ := (mem_autI hU).1 (hLH hgL)
      have hg'M : (g' : G) ∈ M := hH₀M hg'H
      have hcM : g⁻¹ * (g' : G) ∈ M := M.mul_mem (M.inv_mem hgM) hg'M
      have hcN : g⁻¹ * (g' : G) ∈ Subgroup.normalizer (V : Set G) := hMN hcM
      have hcC0 : g⁻¹ * (g' : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [← convI_eq_one_iff hU ⟨_, hcN⟩]
        have : (⟨g⁻¹ * (g' : G), hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            (⟨g, hMN hgM⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * g' := Subtype.ext rfl
        rw [this, map_mul, map_inv, hg'e]
        have h2 : convI hU ⟨g, hMN hgM⟩ = actM hU hMN ⟨g, hgM⟩ := rfl
        rw [h2, inv_mul_cancel]
      have hcC : g⁻¹ * (g' : G) ∈ C' := ⟨hcC0, hcM⟩
      have hy' : (g' : G) * x * (g' : G)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H₀ hg'H) x).mp hx
      have hxM : x ∈ M := hYM hx
      have hc2 : x * (g⁻¹ * (g' : G)) * x⁻¹ * (g⁻¹ * (g' : G))⁻¹ ∈ C' := by
        have h1 : x * (g⁻¹ * (g' : G)) * x⁻¹ ∈ C' :=
          (Subgroup.mem_normalizer_iff.mp (hCM hxM) _).mp hcC
        exact C'.mul_mem h1 (C'.inv_mem hcC)
      have hc3 : g * (x * (g⁻¹ * (g' : G)) * x⁻¹ * (g⁻¹ * (g' : G))⁻¹) * g⁻¹ ∈ C' := by
        have := (Subgroup.mem_normalizer_iff.mp (hCM hgM) _).mp hc2
        exact this
      have e : g * x * g⁻¹ = (g * (x * (g⁻¹ * (g' : G)) * x⁻¹ * (g⁻¹ * (g' : G))⁻¹) * g⁻¹) *
          ((g' : G) * x * (g' : G)⁻¹) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_right hc3) (Subgroup.mem_sup_left hy')
    have hCS : ∀ c ∈ C', g * c * g⁻¹ ∈ S := fun c hc =>
      Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hCM hgM) c).mp hc)
    have h : S ≤ S.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_comap]; simpa [MulAut.conj_apply] using hYS x hx
      · rw [Subgroup.mem_comap]; simpa [MulAut.conj_apply] using hCS c hc
    intro x hx
    simpa [MulAut.conj_apply] using h hx
  have hKN : K ≤ Subgroup.normalizer (S : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hkey g hg x hx
    · intro hx
      have := hkey g⁻¹ (inv_mem hg) _ hx
      simpa [mul_assoc] using this
  have hSn : (S.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).2 hKN
  have hYn : (Y.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 B.sup_le_normalizer
  have hKK : K ≤ preAutM hU hMN (⨆ L' ∈ I, L') := ctx.preAutM_le_preAutM_iSup hL
  have hKn : (K.subgroupOf (preAutM hU hMN (⨆ L' ∈ I, L'))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKK).2 (ctx.preAutM_iSup_le_normalizer_preAutM hL)
  have hJn : ((preAutM hU hMN (⨆ L' ∈ I, L')).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (preAutM_le hU hMN _)).2
      ctx.M_le_normalizer_preAutM_iSup
  exact IsSubnormal.step le_sup_left hYn
    (IsSubnormal.step hSK hSn (IsSubnormal.step hKK hKn
      (IsSubnormal.step (preAutM_le hU hMN _) hJn (IsSubnormal.refl M))))

end Ctx2

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
