module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.Quasithin.Background.F6ResL28
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.Open CFSG.AGLEmbedding

namespace SylowThreeAbelian

open CFSG.Quasithin.F6.L28Res

theorem g9_centralizer_check : ∀ g : G8, g * g9 = g9 * g → ∃ j : Fin 9, g = g9 ^ (j : ℕ) := by
  decide +kernel

theorem frob_g9_check : ∀ g : G8, g * frobF g9 * g⁻¹ ≠ g9 := by
  decide +kernel

theorem frob_apply (x : G8) : frob x = frobF x := rfl

theorem g8_center (x : G8) (h : ∀ y : G8, x * y = y * x) : x = 1 :=
  eq_one_of_commute x (h ga) (h gb)

theorem card_mulAut_G8 : Nat.card (MulAut G8) = 3 * Nat.card G8 := by
  rw [card_mulAut, card_G8]

theorem frob_outer (g : G8) : MulAut.conj g ≠ frob := by
  intro h
  refine (frob_not_inner g).1 ⟨?_, ?_⟩
  · rw [← MulAut.conj_apply, h]
    rfl
  · rw [← MulAut.conj_apply, h]
    rfl

theorem eq_conj_of_fix (α : MulAut G8) (hα : α g9 = g9) :
    ∃ j : Fin 9, α = MulAut.conj (g9 ^ (j : ℕ)) := by
  by_cases hin : ∃ g : G8, MulAut.conj g = α
  · obtain ⟨g, rfl⟩ := hin
    have h1 : g * g9 * g⁻¹ = g9 := by simpa only [MulAut.conj_apply] using hα
    have h2 : g * g9 = g9 * g := by
      calc g * g9 = g * g9 * g⁻¹ * g := by group
        _ = g9 * g := by rw [h1]
    obtain ⟨j, rfl⟩ := g9_centralizer_check g h2
    exact ⟨j, rfl⟩
  · simp only [not_exists] at hin
    have hfix : ∀ β : MulAut G8, β g9 = g9 → ∀ g : G8, β ≠ MulAut.conj g * frob := by
      intro β hβ g hg
      apply frob_g9_check g
      rw [hg, MulAut.mul_apply, frob_apply, MulAut.conj_apply] at hβ
      exact hβ
    rcases l28m_exists_conj_mul_of_outer g8_center card_mulAut_G8 frob_outer hin with
      ⟨g, hg⟩ | ⟨g, hg⟩
    · exact absurd hg (hfix α hα g)
    · refine absurd hg (hfix α⁻¹ ?_ g)
      calc α⁻¹ g9 = α⁻¹ (α g9) := by rw [hα]
        _ = g9 := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem nonempty_psl2GF_equiv_G8 : Nonempty (PSL2GF 2 3 ≃* G8) := by
  obtain ⟨e⟩ := nonempty_equiv (GaloisField 2 3) (by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num)
  exact ⟨(CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    (GaloisField 2 3)).trans e⟩

@[expose] noncomputable def conjHom {X : Type} [Group X] (K : Subgroup X) [K.Normal]
    (θ : K ≃* G8) : X →* MulAut G8 :=
  (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal

theorem conjHom_apply {X : Type} [Group X] (K : Subgroup X) [K.Normal] (θ : K ≃* G8) (x : X)
    (k : K) : conjHom K θ x (θ k) = θ (MulAut.conjNormal x k) := by
  simp [conjHom, MulAut.congr_apply]

theorem conjHom_injective {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (θ : K ≃* G8) :
    Function.Injective (conjHom K θ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := conjHom_apply K θ x ⟨k, hk⟩
    rw [hx, MulAut.one_apply] at h1
    have h2 : x * k * x⁻¹ = k := by
      have := congrArg Subtype.val (θ.injective h1)
      simpa using this.symm
    calc k * x = x * k * x⁻¹ * x := by rw [h2]
      _ = x * k := by group
  rw [hC] at hxC
  exact Subgroup.mem_bot.mp hxC

theorem orderOf_g9 : orderOf g9 = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, h93, h99⟩ := gen_facts_prod
  exact orderOf_eq_prime_pow (n := 1) (p := 3) (by simpa using h93) (by simpa using h99)

theorem false_of_comm_e9 {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (θ : K ≃* G8) (R : Sylow 3 X)
    (hcomm : ∀ x ∈ (R : Subgroup X), ∀ y ∈ (R : Subgroup X), x * y = y * x)
    {E : Subgroup X} (hER : E ≤ R) (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := conjHom_injective hC θ
  have hq9 : orderOf ((θ.symm g9 : K) : X) = 9 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective θ.toMonoidHom θ.injective,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, orderOf_g9]
  have hp : IsPGroup 3 (Subgroup.zpowers ((θ.symm g9 : K) : X)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hq9]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq X Q R
  have hRQ : (R : Subgroup X) = (Q : Subgroup X).map (MulAut.conj y).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul]
    rfl
  have hkR : y * ((θ.symm g9 : K) : X) * y⁻¹ ∈ (R : Subgroup X) := by
    rw [hRQ]
    exact ⟨_, hQ (Subgroup.mem_zpowers _), rfl⟩
  have hkK : y * ((θ.symm g9 : K) : X) * y⁻¹ ∈ K :=
    ‹K.Normal›.conj_mem _ (θ.symm g9).2 y
  have hθk : θ ⟨_, hkK⟩ = conjHom K θ y g9 := by
    calc θ ⟨_, hkK⟩ = θ (MulAut.conjNormal y (θ.symm g9)) := rfl
      _ = conjHom K θ y (θ (θ.symm g9)) := (conjHom_apply K θ y _).symm
      _ = conjHom K θ y g9 := by rw [MulEquiv.apply_symm_apply]
  have hfix : ∀ x ∈ (R : Subgroup X), conjHom K θ x (conjHom K θ y g9) = conjHom K θ y g9 := by
    intro x hx
    rw [← hθk, conjHom_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show x * (y * ((θ.symm g9 : K) : X) * y⁻¹) * x⁻¹ = y * ((θ.symm g9 : K) : X) * y⁻¹
    rw [hcomm x hx _ hkR]
    group
  have key : ∀ x ∈ (R : Subgroup X), ∃ j : Fin 9,
      conjHom K θ x = conjHom K θ y * MulAut.conj (g9 ^ (j : ℕ)) * (conjHom K θ y)⁻¹ := by
    intro x hx
    obtain ⟨j, hj⟩ := eq_conj_of_fix ((conjHom K θ y)⁻¹ * conjHom K θ x * conjHom K θ y) (by
      rw [MulAut.mul_apply, MulAut.mul_apply, hfix x hx, ← MulAut.mul_apply, inv_mul_cancel,
        MulAut.one_apply])
    refine ⟨j, ?_⟩
    rw [← hj]
    group
  have hcard : Nat.card (R : Subgroup X) ≤ 9 := by
    choose f hf using key
    have hfinj : Function.Injective (fun x : (R : Subgroup X) => f x.1 x.2) := by
      intro a b hab
      apply Subtype.ext
      apply hinj
      rw [hf a.1 a.2, hf b.1 b.2]
      simp only at hab
      rw [hab]
    calc Nat.card (R : Subgroup X) ≤ Nat.card (Fin 9) := Nat.card_le_card_of_injective _ hfinj
      _ = 9 := Nat.card_fin 9
  have hRE : E = R := Subgroup.eq_of_le_of_card_ge hER (by rw [hE9]; exact hcard)
  have hk3 : (y * ((θ.symm g9 : K) : X) * y⁻¹) ^ 3 = 1 := hE.2 _ (by rw [hRE]; exact hkR)
  have h3 : (θ ⟨_, hkK⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨_, hkK⟩ : K) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk3)
    rw [this, map_one]
  rw [hθk, ← map_pow] at h3
  exact gen_facts_prod.2.2.1 ((MulEquiv.map_eq_one_iff _).mp h3)

theorem kFactSylowThreeAbelian_psl28 :
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (R : Sylow 3 X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* PSL2GF 2 3) →
      (∀ x ∈ (R : Subgroup X), ∀ y ∈ (R : Subgroup X), x * y = y * x) →
      (∃ E : Subgroup X, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) →
      IsElemAbelian 3 (R : Subgroup X) ∧ Nat.card (R : Subgroup X) = 9 := by
  intro X _ _ K R hKn hC ⟨e⟩ hcomm ⟨E, hER, hE, hE9⟩
  have : K.Normal := hKn
  obtain ⟨β⟩ := nonempty_psl2GF_equiv_G8
  exact (false_of_comm_e9 hC (e.trans β) R hcomm hER hE hE9).elim

end SylowThreeAbelian

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
