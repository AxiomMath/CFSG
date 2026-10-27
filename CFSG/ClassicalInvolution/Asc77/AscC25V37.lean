module

public import CFSG.ClassicalInvolution.Asc77.AscC25V33
public import CFSG.ClassicalInvolution.Asc77.AscC25V34
public import CFSG.ClassicalInvolution.Asc77.AscC25V19
public import CFSG.ClassicalInvolution.Asc77.AscC25Y6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem fieldChar_eq_one_of_comm_mod_odd {p f : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {k : G}
    (hkN : k ∈ Subgroup.normalizer (K : Set G)) (hk : ∀ l ∈ K, ⁅k, l⁆ ∈ oddCoreOf K) :
    fieldChar hp hq e ⟨k, hkN⟩ = 1 := by
  have h1 : normalizerToPGammaL2Mod e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1
      (gf_facts hp hq).2.2.2 ⟨k, hkN⟩ = 1 := by
    rw [Hall196.normalizerToPGammaL2Mod_eq_one_iff]
    exact hk
  change SemidirectProduct.rightHom (normalizerToPGammaL2Mod e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 ⟨k, hkN⟩) = 1
  rw [h1, map_one]

theorem exists_fixed_lift {Z : Type*} [Group Z] [Finite Z] (O : Subgroup Z) [O.Normal]
    (hO : Odd (Nat.card O)) {ζ : Z} (hζ : ζ * ζ = 1) {x₀ : Z}
    (hx : (QuotientGroup.mk (ζ * x₀ * ζ⁻¹) : Z ⧸ O) = QuotientGroup.mk x₀) :
    ∃ t₀ : Z, (QuotientGroup.mk t₀ : Z ⧸ O) = QuotientGroup.mk x₀ ∧ ζ * t₀ * ζ⁻¹ = t₀ := by
  classical
  let := Fintype.ofFinite Z
  let α : Type _ := {x : Z // (QuotientGroup.mk x : Z ⧸ O) = QuotientGroup.mk x₀}
  have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ
  have hmem : ∀ x : α, (QuotientGroup.mk (ζ * x.1 * ζ⁻¹) : Z ⧸ O) = QuotientGroup.mk x₀ := by
    intro x
    have h1 := (QuotientGroup.eq.mp x.2)
    have h2 := (QuotientGroup.eq.mp hx)
    rw [QuotientGroup.eq]
    have h3 : (ζ * x.1 * ζ⁻¹)⁻¹ * x₀ = (ζ * x.1 * ζ⁻¹)⁻¹ * (ζ * x₀ * ζ⁻¹) *
        ((ζ * x₀ * ζ⁻¹)⁻¹ * x₀) := by group
    rw [h3]
    refine Subgroup.mul_mem _ ?_ h2
    have h4 : (ζ * x.1 * ζ⁻¹)⁻¹ * (ζ * x₀ * ζ⁻¹) = ζ * (x.1⁻¹ * x₀) * ζ⁻¹ := by group
    rw [h4]
    have : ζ * (x.1⁻¹ * x₀) * ζ⁻¹ ∈ O := (inferInstance : O.Normal).conj_mem _ (by
      have := (QuotientGroup.eq.mp x.2)
      exact this) ζ
    exact this
  let σ : Equiv.Perm α :=
    { toFun := fun x => ⟨ζ * x.1 * ζ⁻¹, hmem x⟩
      invFun := fun x => ⟨ζ * x.1 * ζ⁻¹, hmem x⟩
      left_inv := fun x => Subtype.ext (by
        change ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = x.1
        calc ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * x.1 * (ζ * ζ)⁻¹ := by group
          _ = x.1 := by rw [hζ]; group)
      right_inv := fun x => Subtype.ext (by
        change ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = x.1
        calc ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * x.1 * (ζ * ζ)⁻¹ := by group
          _ = x.1 := by rw [hζ]; group) }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext x
    change ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = x.1
    calc ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * x.1 * (ζ * ζ)⁻¹ := by group
      _ = x.1 := by rw [hζ]; group
  have hcard : Nat.card α = Nat.card O := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * x.1, QuotientGroup.eq.mp x.2.symm⟩
        invFun := fun o => ⟨x₀ * o.1, by
          rw [QuotientGroup.eq]
          simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, hcard]
    have := Nat.odd_iff.mp hO
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxσ⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ2
  refine ⟨x.1, x.2, ?_⟩
  have := congrArg Subtype.val hxσ
  exact this

omit [Finite G] in
theorem conjSub_perfectCoreIn_eq {K : Subgroup G} {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) (hcK : c ∈ Subgroup.normalizer (K : Set G)) :
    conjSub (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K a) =
      perfectCoreIn K a := by
  have hnN : c ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
    change conjSub c K ⊓ conjSub c (Subgroup.centralizer ({a} : Set G)) = _
    rw [conjSub_eq_of_mem_normalizer hcK,
      conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hc)]
  have h1 := conjSub_eq_of_mem_normalizer (perfectResidualOf_normalizer_contains _ hnN)
  unfold perfectCoreIn
  rw [conjSub_subgroupOf _ ⟨c, hc⟩, h1]

theorem fieldChar_comm_formula {p f : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {d t₀ t' : G} (ht'2 : t' * t' = 1) (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hd' : t' * d * t' ∈ Subgroup.normalizer (K : Set G))
    (hc : t₀ * t' ∈ Subgroup.normalizer (K : Set G))
    (hy : d * t₀ * d⁻¹ * t₀⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    fieldChar hp hq e ⟨d * t₀ * d⁻¹ * t₀⁻¹, hy⟩ =
      fieldChar hp hq e ⟨d, hdK⟩ * (fieldChar hp hq e ⟨t' * d * t', hd'⟩)⁻¹ := by
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  have ht'i : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have key : (t₀ * t') * (t' * d * t') * (t₀ * t')⁻¹ = t₀ * d * t₀⁻¹ := by
    rw [mul_inv_rev, ht'i]
    calc t₀ * t' * (t' * d * t') * (t' * t₀⁻¹) = t₀ * (t' * t') * d * (t' * t') * t₀⁻¹ := by group
      _ = t₀ * d * t₀⁻¹ := by rw [ht'2]; group
  have e1 : (⟨d * t₀ * d⁻¹ * t₀⁻¹, hy⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨d, hdK⟩ * (⟨t₀ * t', hc⟩ * ⟨t' * d * t', hd'⟩ * ⟨t₀ * t', hc⟩⁻¹)⁻¹ := by
    apply Subtype.ext
    change d * t₀ * d⁻¹ * t₀⁻¹ = d * ((t₀ * t') * (t' * d * t') * (t₀ * t')⁻¹)⁻¹
    rw [key]
    group
  rw [e1, map_mul, map_inv, map_mul, map_mul, map_inv]
  rw [mul_comm (fieldChar hp hq e ⟨t₀ * t', hc⟩), mul_assoc, mul_inv_cancel, mul_one]

end Basic

section Omega5

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


theorem fieldChar_eq_one_of_mem_join (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
    {x : ↥(Subgroup.centralizer ({a} : Set G))}
    (hx : x ∈ perfectCoreIn K' a ⊔ conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G)))
      (perfectCoreIn K' a))
    : ∃ hxN : (x : G) ∈ Subgroup.normalizer (K : Set G), fieldChar hp hq e ⟨x, hxN⟩ = 1 := by
  classical
  let Kc : Subgroup G :=
    (MonoidHom.ker (fieldChar hp hq e)).map (Subgroup.normalizer (K : Set G)).subtype
  have hKc' : ∀ g ∈ Kc, ∃ hg : g ∈ Subgroup.normalizer (K : Set G),
      fieldChar hp hq e ⟨g, hg⟩ = 1 := by
    rintro g ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  let Mc : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    Kc.comap (Subgroup.centralizer ({a} : Set G)).subtype
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    h.hΩ.le_normalizer_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz
  have hcomm := h.hΩ.comm_le_oddCore_of_twin h.hK h.hK' h.hs.hne.symm h.hz h.hz'
  have hL1 : perfectCoreIn K' a ≤ Mc := by
    intro g hg
    have hgK' : (g : G) ∈ K' :=
      ((perfectResidualOf_le _).trans inf_le_left) (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨⟨g, hK'N hgK'⟩, ?_, rfl⟩
    refine fieldChar_eq_one_of_comm_mod_odd hp hq e (hK'N hgK') (fun l hl => ?_)
    have h1 : ⁅l, (g : G)⁆ ∈ oddCoreOf K :=
      (hcomm (Subgroup.commutator_mem_commutator hl hgK')).1
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ h1
  have hL2 : conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K' a) ≤
      Mc := by
    rintro _ ⟨g₀, hg₀, rfl⟩
    have hg₀K' : (g₀ : G) ∈ K' :=
      ((perfectResidualOf_le _).trans inf_le_left) (Subgroup.mem_subgroupOf.mp hg₀)
    have hmem : t' * (g₀ : G) * t'⁻¹ ∈ K := by
      have := conj_mem_conjSub (n := t') hg₀K'
      rwa [conjSub_t'_K' h] at this
    refine ⟨⟨t' * (g₀ : G) * t'⁻¹, Subgroup.le_normalizer hmem⟩, ?_, rfl⟩
    exact fieldChar_eq_one_of_mem hp hq e hmem (Subgroup.le_normalizer hmem)
  exact hKc' (x : G) (sup_le hL1 hL2 hx)

local notation "Lₐ" => perfectCoreIn K' a

theorem g1_omega5 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a) (hat : a * t' = t' * a)
    {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hO5 : SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a))
      (conjGen (perfectCoreIn K' a)) 5 true)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G)) (hdz : d * z = z * d)
    (hda : d * a = a * d) (hd' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)) :
    Odd (orderOf (fieldChar hp hq e ⟨d, hdK⟩ * (fieldChar hp hq e ⟨t' * d * t', hd'⟩)⁻¹)) := by
  classical
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := fs_twinSect0 h h9 haS ha2 hF' hat h5 hzA hL
  obtain ⟨tg, n, hT, D, hcard, i, hi1, hi2⟩ := hO5
  have hXn : (conjGen (perfectCoreIn K' a)).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hcent := twinCent5_proved (p := p) (f := e₀) hp
    (↥(conjGen (perfectCoreIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a)))
    _ D _ _ _ a₀ b₀ hcard ⟨i, by rw [hi1, hi2]; exact hT⟩ T
  obtain ⟨⟨sw, hs1, hs2, hs3⟩, hy⟩ := hcent
  let w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩
  let ζ : ↥(conjGen Lₐ) := ⟨⟨z, hzA⟩, hzX⟩
  have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
  have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
  have hL'mem : conjSub w Lₐ ∈ conjFamily Lₐ := ⟨w, rfl⟩
  have hL'X : conjSub w Lₐ ≤ conjGen Lₐ := le_conjGen hL'mem
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hzz
  have hdC : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hda
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective sw
  have hx : (QuotientGroup.mk (ζ * x₀ * ζ⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = QuotientGroup.mk x₀ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx₀]
    change QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩ * sw * (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩)⁻¹ = sw
    rw [mul_inv_eq_iff_eq_mul]
    exact hs1.symm
  obtain ⟨t₀, ht₀s, ht₀z⟩ := exists_fixed_lift _ hOodd hζ2 hx
  have hsw1 : (QuotientGroup.mk t₀ :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = sw := ht₀s.trans hx₀
  have ht₀zz : (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) * z =
      z * (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) := by
    have h1 : ζ * t₀ = t₀ * ζ := mul_inv_eq_iff_eq_mul.mp ht₀z
    have h2 := congrArg (fun x : ↥(conjGen Lₐ) =>
      ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G)) h1
    exact h2.symm
  obtain ⟨t₀G, ht₀G⟩ : ∃ g : G,
      g = (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) := ⟨_, rfl⟩
  rw [← ht₀G] at ht₀zz
  have ht₀C : t₀G ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [ht₀G]
    exact ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hnotN : conjSub t₀G K ≠ K := by
    intro hN
    have ht'K : conjSub t' K = K' := by
      have := congrArg (conjSub t') (conjSub_t'_K' h)
      rw [← conjSub_mul, h.ht'2, conjSub_one] at this
      exact this.symm
    have hc1 : conjSub (t' * t₀G * t') K' = K' := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K' h, hN, ht'K]
    have hcC : t' * t₀G * t' ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ht'a ht₀C) ht'a
    have hfix := conjSub_perfectCoreIn_eq (K := K') hcC (mem_normalizer_iff_conjSub_eq.mpr hc1)
    have h1 : conjSub ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
        (conjSub w Lₐ) = conjSub w Lₐ := by
      have e2 : ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) * w =
          w * (⟨t' * t₀G * t', hcC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
        apply Subtype.ext
        change (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) * t' =
          t' * (t' * t₀G * t')
        rw [← ht₀G]
        calc t₀G * t' = (t' * t') * t₀G * t' := by rw [h.ht'2]; group
          _ = t' * (t' * t₀G * t') := by group
      rw [← conjSub_mul, e2, conjSub_mul, hfix]
    have hsecw : conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ)) =
        secImg (conjGen Lₐ) (conjSub w Lₐ) := by
      have h2 := secAct_secImg (conjGen Lₐ)
        ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) hL'X
      rw [h1] at h2
      calc conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ))
          = (secImg (conjGen Lₐ) (conjSub w Lₐ)).map (secAct (conjGen Lₐ)
              ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))).toMonoidHom := by
            rw [secAct_of_mem (conjGen Lₐ) (t₀ : ↥(conjGen Lₐ)).2, ← hsw1]
            rfl
        _ = secImg (conjGen Lₐ) (conjSub w Lₐ) := h2
    rw [hsecw] at hs3
    exact T.ne hs3.symm
  have hsw' : conjSub (t₀G * t') K = K := by
    rcases cz_cover h ht₀zz with h1 | h1
    · exact absurd h1 hnotN
    · exact h1
  let d₀ : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨d, hdC⟩
  let u : ↥(conjGen Lₐ) :=
    ⟨d₀ * ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) * d₀⁻¹,
      hXn.conj_mem _ t₀.2 d₀⟩
  let y₁ : ↥(conjGen Lₐ) := u * t₀⁻¹
  have hy₁G : (((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) =
      d * t₀G * d⁻¹ * t₀G⁻¹ := by
    rw [ht₀G]
    rfl
  have hd'z : d⁻¹ * z = z * d⁻¹ := by
    calc d⁻¹ * z = d⁻¹ * (z * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * z) * d⁻¹ := by rw [hdz]
      _ = z * d⁻¹ := by group
  have hy₁z : (d * t₀G * d⁻¹ * t₀G⁻¹) * z = z * (d * t₀G * d⁻¹ * t₀G⁻¹) := by
    have c1 : Commute z d := hdz.symm
    have c2 : Commute z t₀G := ht₀zz.symm
    exact (((c1.mul_right c2).mul_right c1.inv_right).mul_right c2.inv_right).eq.symm
  have hy₁K : d * t₀G * d⁻¹ * t₀G⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    have h1 : t₀G * d⁻¹ * t₀G⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
      have := (twinCtx_of_hyp25 h).conj_normalizer ht₀zz hd'z
        (by
          have := Subgroup.inv_mem _ hdK
          exact mem_normalizer_iff_conjSub_eq.mp this)
      exact mem_normalizer_iff_conjSub_eq.mpr this
    have h2 := Subgroup.mul_mem _ hdK h1
    simpa [mul_assoc] using h2
  have hy₁K' : d * t₀G * d⁻¹ * t₀G⁻¹ ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      ((twinCtx_of_hyp25 h).conj_iff hy₁z |>.mp (mem_normalizer_iff_conjSub_eq.mp hy₁K))
  have hy₁C : d * t₀G * d⁻¹ * t₀G⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [← hy₁G]
    exact ((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hy₁L : conjSub ((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ = Lₐ :=
    by
    have e : ((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) =
        ⟨d * t₀G * d⁻¹ * t₀G⁻¹, hy₁C⟩ := Subtype.ext hy₁G
    rw [e]
    exact conjSub_perfectCoreIn_eq (K := K') hy₁C hy₁K'
  have hbz : (QuotientGroup.mk y₁ :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) * QuotientGroup.mk ζ =
      QuotientGroup.mk ζ * QuotientGroup.mk y₁ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    have e1 : ((((y₁ * ζ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G)) =
        (((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) * z := rfl
    have e2 : ((((ζ * y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G)) =
        z * (((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) := rfl
    rw [e1, e2, hy₁G]
    exact hy₁z
  have hbA : conjSub (QuotientGroup.mk y₁ :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) (secImg (conjGen Lₐ) Lₐ) =
      secImg (conjGen Lₐ) Lₐ := by
    have h2 := secAct_secImg (conjGen Lₐ)
      ((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) hLX
    rw [hy₁L] at h2
    calc conjSub (QuotientGroup.mk y₁ :
          ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) (secImg (conjGen Lₐ) Lₐ)
        = (secImg (conjGen Lₐ) Lₐ).map (secAct (conjGen Lₐ)
            ((y₁ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))).toMonoidHom := by
          rw [secAct_of_mem (conjGen Lₐ) (y₁ : ↥(conjGen Lₐ)).2]
          rfl
      _ = secImg (conjGen Lₐ) Lₐ := h2
  have hmem := hy _ hbz hbA
  have hjoin : secImg (conjGen Lₐ) Lₐ ⊔ secImg (conjGen Lₐ) (conjSub w Lₐ) =
      secImg (conjGen Lₐ) (Lₐ ⊔ conjSub w Lₐ) := by
    unfold secImg
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLX hL'X]
  rw [hjoin] at hmem
  obtain ⟨xx, hxx, hxxy⟩ := hmem
  have hxo : xx⁻¹ * y₁ ∈ classicalInvolutionOddCore ↥(conjGen Lₐ) := by
    have := QuotientGroup.eq.mp hxxy
    exact this
  obtain ⟨hxxN', hxxχ'⟩ := fieldChar_eq_one_of_mem_join h hp hq e ht'a
    (x := ((xx : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))))
    (Subgroup.mem_subgroupOf.mp hxx)
  let xG : G := (((xx : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G)
  have hxxN : xG ∈ Subgroup.normalizer (K : Set G) := hxxN'
  have hxxχ : fieldChar hp hq e ⟨xG, hxxN⟩ = 1 := hxxχ'
  let oG : G := ((((xx⁻¹ * y₁ : ↥(conjGen Lₐ))) :
      ↥(Subgroup.centralizer ({a} : Set G))) : G)
  have hy₁xo : d * t₀G * d⁻¹ * t₀G⁻¹ = xG * oG := by
    rw [← hy₁G]
    have : xx * (xx⁻¹ * y₁) = y₁ := by group
    conv_lhs => rw [← this]
    rfl
  have hooN : oG ∈ Subgroup.normalizer (K : Set G) := by
    have : oG = xG⁻¹ * (d * t₀G * d⁻¹ * t₀G⁻¹) := by rw [hy₁xo]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxxN) hy₁K
  have hooodd : Odd (orderOf oG) := by
    let oo : ↥(classicalInvolutionOddCore ↥(conjGen Lₐ)) := ⟨xx⁻¹ * y₁, hxo⟩
    have h1 : orderOf oo ∣ Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ)) :=
      orderOf_dvd_natCard oo
    have e1 : orderOf oG = orderOf (((xx⁻¹ * y₁ : ↥(conjGen Lₐ))) :
        ↥(Subgroup.centralizer ({a} : Set G))) := Subgroup.orderOf_coe _
    have e2 : orderOf (((xx⁻¹ * y₁ : ↥(conjGen Lₐ))) :
        ↥(Subgroup.centralizer ({a} : Set G))) = orderOf (xx⁻¹ * y₁) := Subgroup.orderOf_coe _
    have e3 : orderOf (xx⁻¹ * y₁ : ↥(conjGen Lₐ)) = orderOf oo := Subgroup.orderOf_coe oo
    rw [e1, e2, e3]
    exact Odd.of_dvd_nat hOodd h1
  have hfinal : fieldChar hp hq e ⟨d * t₀G * d⁻¹ * t₀G⁻¹, hy₁K⟩ =
      fieldChar hp hq e ⟨oG, hooN⟩ := by
    have e1 : (⟨d * t₀G * d⁻¹ * t₀G⁻¹, hy₁K⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨xG, hxxN⟩ * ⟨oG, hooN⟩ := Subtype.ext hy₁xo
    rw [e1, map_mul, hxxχ, one_mul]
  have hcomm := fieldChar_comm_formula hp hq e h.ht'2 hdK hd'
    (mem_normalizer_iff_conjSub_eq.mpr hsw') hy₁K
  rw [← hcomm, hfinal]
  have h1 : orderOf (fieldChar hp hq e ⟨oG, hooN⟩) ∣
      orderOf (⟨oG, hooN⟩ : Subgroup.normalizer (K : Set G)) := orderOf_map_dvd _ _
  have h2 : orderOf (⟨oG, hooN⟩ : Subgroup.normalizer (K : Set G)) = orderOf oG :=
    (Subgroup.orderOf_coe (⟨oG, hooN⟩ : Subgroup.normalizer (K : Set G))).symm
  rw [h2] at h1
  exact Odd.of_dvd_nat hooodd h1

end Omega5

end CFSG.ClassicalInvolution.Asc77.C25V
