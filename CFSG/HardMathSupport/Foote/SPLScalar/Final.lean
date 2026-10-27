module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThree
public import CFSG.HardMathSupport.Foote.SPLScalar.Torus
public import CFSG.HardMathSupport.Foote.SPLScalar.Cases
public import CFSG.HardMathSupport.Foote.SPLScalar.CasesAltSix
public import CFSG.HardMathSupport.Foote.SPLScalar.Frattini

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.AGLEmbedding CFSG.Open

@[expose] def UnitarySingerStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), IsUnitaryIndex 3 d →
    2 ≤ d.1.fieldExponent → Even d.1.fieldExponent → Nonempty (K ≃* CatGroup d) →
    ∀ (T : Sylow 3 K) (E : Subgroup K), E ≤ T → IsElemAbelian 3 E → Nat.card E = 9 →
    ¬ E ≤ Subgroup.centralizer ((T : Subgroup K) : Set K) →
    ∀ w : K, w ∈ Subgroup.normalizer (E : Set K) → (∀ a ∈ E, w ^ 2 * a * (w ^ 2)⁻¹ = a⁻¹) →
    ∃ c ∈ Subgroup.normalizer (E : Set K), (∀ a ∈ E, c ^ 4 * a * (c ^ 4)⁻¹ = a ^ 2) ∧
      ∀ k, 0 < k → k < 4 → ∀ F : Subgroup K, F ≤ E → F.relIndex E = 3 →
        c ^ k ∉ Subgroup.normalizer (F : Set K)

theorem altSix_or_unitaryThree {L : Type} [Group L] (hL : IsSPLFamily 3 L) :
    IsAltTwoP 3 L ∨ IsSmallUnitary 3 L := by
  rcases hL with h | h | ⟨-, h⟩
  · exact Or.inl (isAltTwoP_of_isSmallLinTwo_three h)
  · exact Or.inr h
  · exact Or.inl h

theorem conclusion_of_torus {KC : Type} [Group KC] [Finite KC] {n e : ℕ} (hn : 2 ≤ n)
    (he : e = 1 ∨ (e = 2 ∧ 3 ≤ n ∧ Even n)) (ψ : Multiplicative (GaloisField 3 n) →* KC)
    (htor : ∀ μ : (GaloisField 3 n)ˣ, ∃ c : KC, ∀ a, c * ψ a * c⁻¹ =
      ψ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ e * Multiplicative.toAdd a)))
    {T' E : Subgroup KC} (hψT : ψ.range = T' ⊓ Subgroup.centralizer (T' : Set KC))
    (hEψ : E ⊓ Subgroup.centralizer (E : Set KC) ≤ ψ.range) :
    ∃ A : Subgroup KC, A ≤ T' ∧ IsElemAbelian 3 A ∧
      E ⊓ Subgroup.centralizer (E : Set KC) ≤ A ∧
      ∃ c ∈ Subgroup.normalizer (A : Set KC), ∃ m lam : ℕ, 5 ≤ 2 * m ∧ ¬ 3 ∣ lam - 1 ∧
        (∀ a ∈ A, c ^ m * a * (c ^ m)⁻¹ = a ^ lam) ∧
        ∀ k, 0 < k → k < m → ∀ F : Subgroup KC, F ≤ A → F.relIndex A = 3 →
          c ^ k ∉ Subgroup.normalizer (F : Set KC) := by
  obtain ⟨hA, c, hcN, m, lam, hm5, hlam, hact, hhyp⟩ := exists_scalar_of_torus hn he ψ htor
  exact ⟨ψ.range, hψT ▸ inf_le_left, hA, hEψ, c, hcN, m, lam, hm5, hlam, hact, hhyp⟩

theorem kFactSPLInvolveScalar_of_singer
    (hS : UnitarySingerStatement) (hId : KFactOneLieIdent) : KFactSPLInvolveScalar := by
  intro KC _ _ hs hnab hcat T hT hΓ hrk W L _ _ hL f hf hker E hEW hE hTL T' hET'
  obtain ⟨TL, hTL⟩ := hTL
  have hL' := altSix_or_unitaryThree hL
  have hEL : Nonempty (↥E ≃* ↥(TL : Subgroup L)) := nonempty_mulEquiv_of_map_eq f hker hEW hE hTL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hfam, he⟩ :=
    hId KC hs hnab hcat 3 Nat.prime_three (by norm_num) T hT hΓ (by omega)
  rcases hfam with ⟨n, hn, hdn⟩ | ⟨hdU, hn⟩ | hdR
  · rcases hL' with hA6 | hU3
    · have hev : Even n := even_of_lin_altSix (by omega) hdn he hA6 f hf
      obtain ⟨e₁⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdn
      obtain ⟨eK⟩ := he
      obtain ⟨ψ, -, hψT, hc⟩ := (oneLieTorusFacts_of_psl2GF kFactUnitarySylowStructure
        (by norm_num) hn (eK.trans e₁) T').torus
      have hab : ∀ x ∈ (T' : Subgroup KC), ∀ y ∈ (T' : Subgroup KC), x * y = y * x := by
        set g : KC →* PSL2GF 3 n := (eK.trans e₁).toMonoidHom
        have hgs : Function.Surjective g := (eK.trans e₁).surjective
        have hU : ((T'.mapSurjective hgs : Sylow 3 (PSL2GF 3 n)) : Subgroup (PSL2GF 3 n)) =
            (T' : Subgroup KC).map g := Sylow.coe_mapSurjective hgs T'
        have hcomm := (psl2GF_sylow 3 n (by omega) (T'.mapSurjective hgs)).1.1
        intro x hx y hy
        have hx' : g x ∈ ((T'.mapSurjective hgs : Sylow 3 (PSL2GF 3 n)) : Subgroup _) :=
          hU ▸ ⟨x, hx, rfl⟩
        have hy' : g y ∈ ((T'.mapSurjective hgs : Sylow 3 (PSL2GF 3 n)) : Subgroup _) :=
          hU ▸ ⟨y, hy, rfl⟩
        have h1 := hcomm.is_comm.comm ⟨g x, hx'⟩ ⟨g y, hy'⟩
        have h2 : g (x * y) = g (y * x) := by
          rw [map_mul, map_mul]
          exact congrArg Subtype.val h1
        exact (eK.trans e₁).injective h2
      refine conclusion_of_torus (e := 2) (by omega) (Or.inr ⟨rfl, hn, hev⟩) ψ
        (fun μ => (hc μ).imp fun c hc => hc.2) hψT (inf_le_left.trans ?_)
      rw [hψT]
      refine le_inf hET' fun x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hab y hy x (hET' hx)
    · exact (false_of_lin_unitaryThree (by omega) hdn he hU3 TL T' hET' hEL).elim
  · obtain ⟨ψ, -, hψT, hc⟩ := kFactUnitarySylowCenterTorus KC 3 d hdU he T'
    have htor : ∀ μ : (GaloisField 3 d.1.fieldExponent)ˣ, ∃ c : KC, ∀ a, c * ψ a * c⁻¹ =
        ψ (Multiplicative.ofAdd ((μ : GaloisField 3 d.1.fieldExponent) ^ 1 *
          Multiplicative.toAdd a)) := fun μ => by
      obtain ⟨c, -, hc'⟩ := hc μ
      exact ⟨c, fun a => by rw [hc' a, pow_one]⟩
    rcases hL' with hA6 | hU3
    · by_cases hEZ : E ≤ Subgroup.centralizer ((T' : Subgroup KC) : Set KC)
      · exact conclusion_of_torus hn (Or.inl rfl) ψ htor hψT
          (inf_le_left.trans (hψT ▸ le_inf hET' hEZ))
      · have hev := even_of_unitary_altSix hdU he hA6 f hf
        obtain ⟨hEab, hE9⟩ := Core.elemAbelian_of_altSix f hker hEW hE hA6 TL hTL
        obtain ⟨t, ht, ht2⟩ := exists_sq_inv_of_altSix hA6 TL
        obtain ⟨w, hwt, hwN⟩ := exists_normalizer_lift f hf hker hEW hE hTL ht
        have hw2 := sq_conj_eq_inv_of_map f hker hEW hE hTL ht2 hwt hwN
        obtain ⟨c, hcN, hc4, hck⟩ :=
          hS KC d hdU hn hev he T' E hET' hEab hE9 hEZ _ hwN hw2
        exact ⟨E, hET', hEab, inf_le_left, c, hcN, 4, 2, by norm_num, by norm_num, hc4, hck⟩
    · exact conclusion_of_torus hn (Or.inl rfl) ψ htor hψT
        (hψT ▸ center_le_of_unitary_unitaryThree hdU he hU3 TL T' hET' hEL)
  · exact (false_of_ree hdR he hL' f hf).elim

end CFSG.HardMathSupport.Foote.SPLScalar
