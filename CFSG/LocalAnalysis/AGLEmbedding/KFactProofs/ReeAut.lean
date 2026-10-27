module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeAutCore
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbedding.ReeModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.ComponentClassification.LiteratureLocal.SmallRee

section Card

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem card_mulAut_dvd (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (MulAut ↥(ReeTag.G2.reeGamma K a)) ∣
      Nat.card ↥(ReeTag.G2.reeGamma K a) * (2 * a + 1) := by
  obtain ⟨-, hout⟩ := outer_reeGamma_cyclic ha hK
  have h1 : Nat.card (MulAut ↥(ReeTag.G2.reeGamma K a)) =
      Nat.card (Outer ↥(ReeTag.G2.reeGamma K a)) *
        Nat.card (inner ↥(ReeTag.G2.reeGamma K a)) :=
    (inner ↥(ReeTag.G2.reeGamma K a)).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (inner ↥(ReeTag.G2.reeGamma K a)) ∣ Nat.card ↥(ReeTag.G2.reeGamma K a) :=
    Subgroup.card_range_dvd _
  rw [h1, hout, mul_comm]
  exact Nat.mul_dvd_mul_right h2 _

end Card


section Center

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

private theorem uIn_zero_zero_mem (hK : Nat.card K = 3 ^ (2 * a + 1)) (c : K) :
    uIn hK 0 0 c ∈ stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup
      ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) := by
  rw [← zHom_range hK]
  exact ⟨Multiplicative.ofAdd c, Subtype.ext rfl⟩

theorem eq_conj_of_fixes_center (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (α : MulAut ↥(ReeTag.G2.reeGamma K a))
    (hα : ∀ z ∈ stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup
      ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)), α z = z) :
    ∃ u ∈ stdU a K, α = MulAut.conj u := by
  obtain ⟨g, k, rfl⟩ := exists_eq_conj_mul_frobeniusΓ_pow ha hK α
  have hz : ∀ c : K, g * uIn hK 0 0 (c ^ 3 ^ k) * g⁻¹ = uIn hK 0 0 c := fun c => by
    have h := hα _ (uIn_zero_zero_mem hK c)
    rw [MulAut.mul_apply, frobeniusΓ_pow_uIn, zero_pow (pow_ne_zero _ (by norm_num)),
      MulAut.conj_apply] at h
    exact h
  have hgB : g ∈ stdB a K := by
    by_contra hg
    have hTI := inf_map_conj_eq_bot hK hg
    have h1 : uIn hK 0 0 1 ∈ stdU a K ⊓ (stdU a K).map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (uIn_mem hK 0 0 1), ?_⟩
      refine ⟨uIn hK 0 0 1, Subgroup.mem_subgroupOf.2 (uIn_mem hK 0 0 1), ?_⟩
      have := hz 1
      rw [one_pow] at this
      exact this
    rw [hTI, Subgroup.mem_bot] at h1
    have := uIn_inj hK (h1.trans (uIn_zero hK).symm)
    exact one_ne_zero this.2.2
  have hgB' : (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a :=
    Subgroup.mem_subgroupOf.1 hgB
  rw [← SetLike.mem_coe, (ReeTag.ree_fixed_Bruhat_decomposition ReeTag.G2 a K).2.1] at hgB'
  obtain ⟨u', hu', h, hh, hgeq⟩ := Set.mem_mul.1 hgB'
  obtain ⟨s, hs⟩ := ReeTag.exists_smallReeTorusElt_eq hh
  have hu'Γ : u' ∈ ReeTag.G2.reeGamma K a := ReeTag.reeFixedPosUnipotent_le_reeGamma hu'
  have hu'S : (⟨u', hu'Γ⟩ : ↥(ReeTag.G2.reeGamma K a)) ∈ stdU a K := Subgroup.mem_subgroupOf.2 hu'
  have hgΓ : g = ⟨u', hu'Γ⟩ * hIn hK s := Subtype.ext (by
    rw [Subgroup.coe_mul, hIn_val, ← hgeq, ← hs])
  have hact : ∀ c' : K, g * uIn hK 0 0 c' * g⁻¹ = uIn hK 0 0 ((s : K) ^ 3 ^ a * c') := by
    intro c'
    have h1 := hIn_conj_uIn hK s 0 0 c'
    rw [mul_zero, mul_zero] at h1
    have hcomm := Subgroup.mem_centralizer_iff.1
      (Subgroup.mem_inf.1 (uIn_zero_zero_mem hK ((s : K) ^ 3 ^ a * c'))).2 _ hu'S
    rw [hgΓ]
    calc ⟨u', hu'Γ⟩ * hIn hK s * uIn hK 0 0 c' * (⟨u', hu'Γ⟩ * hIn hK s)⁻¹
        = ⟨u', hu'Γ⟩ * (hIn hK s * uIn hK 0 0 c' * (hIn hK s)⁻¹) * ⟨u', hu'Γ⟩⁻¹ := by group
      _ = ⟨u', hu'Γ⟩ * uIn hK 0 0 ((s : K) ^ 3 ^ a * c') * ⟨u', hu'Γ⟩⁻¹ := by rw [h1]
      _ = uIn hK 0 0 ((s : K) ^ 3 ^ a * c') := by rw [hcomm, mul_inv_cancel_right]
  have hrel : ∀ c : K, (s : K) ^ 3 ^ a * c ^ 3 ^ k = c := fun c => by
    have h1 := hz c
    rw [hact] at h1
    exact (uIn_inj hK h1).2.2
  have hs1 : s = 1 := by
    by_contra hne
    have := hrel 1
    rw [one_pow, mul_one] at this
    exact pow_three_pow_ne_one hK hne this
  subst hs1
  have hk : ∀ x : K, x ^ 3 ^ k = x := fun x => by
    have := hrel x
    rwa [Units.val_one, one_pow, one_mul] at this
  obtain ⟨m, rfl⟩ := dvd_of_forall_pow_three_pow_eq hK hk
  refine ⟨g, ?_, ?_⟩
  · rw [hgΓ]
    have : hIn hK (1 : Kˣ) = 1 :=
      Subtype.ext (by rw [hIn_val, CFSG.Walter.Ree.Model.smallReeH_one]; rfl)
    rw [this, mul_one]
    exact hu'S
  · rw [pow_mul, frobeniusΓ_pow hK, one_pow, mul_one]

end Center


section Rank

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
  {L : Type} [Group L]

theorem center_eq_bot_of_equiv (hK : Nat.card K = 3 ^ (2 * a + 1))
    (e : L ≃* ↥(ReeTag.G2.reeGamma K a)) : Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center ↥(ReeTag.G2.reeGamma K a) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  rw [center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))

theorem conj_injective_of_equiv (hK : Nat.card K = 3 ^ (2 * a + 1))
    (e : L ≃* ↥(ReeTag.G2.reeGamma K a)) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun x hx => ?_)
  have hc : x ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) y
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rwa [center_eq_bot_of_equiv hK e] at hc

theorem isCyclic_outer_of_equiv (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (e : L ≃* ↥(ReeTag.G2.reeGamma K a)) : IsCyclic (Outer L) := by
  have := (outer_reeGamma_cyclic ha hK).1
  exact isCyclic_of_surjective (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    e).symm (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.surjective

variable [Finite L]

theorem card_le_of_pow_three_le_sylow (hK : Nat.card K = 3 ^ (2 * a + 1))
    (e : L ≃* ↥(ReeTag.G2.reeGamma K a)) (T : Sylow 3 L) (D : Subgroup L)
    (hle : D ≤ (T : Subgroup L)) (h3 : ∀ x ∈ D, x ^ 3 = 1) :
    Nat.card D ≤ (3 ^ (2 * a + 1)) ^ 2 ∧ ((3 ^ (2 * a + 1)) ^ 2 < 3 * Nat.card D →
      (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) ≤ D) := by
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := std_facts hK
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e T P
  have hT : (T : Subgroup L).map e'.toMonoidHom = stdU a K := he'.trans hP
  have hD : D.map e'.toMonoidHom ≤ stdU a K := hT ▸ Subgroup.map_mono hle
  have hcard : Nat.card (D.map e'.toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective e'.injective
  obtain ⟨h1, h2⟩ := card_le_of_pow_three_le_stdU hK (D.map e'.toMonoidHom) hD (by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, h3 x hx, map_one])
  rw [hcard] at h1 h2
  refine ⟨h1, fun hlt x hx => ?_⟩
  have hx' : e' x ∈ stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup
      ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) := by
    rw [Subgroup.mem_inf, ← hT, mem_map_iff, mem_centralizer_map_iff]
    exact Subgroup.mem_inf.1 hx
  have := h2 hlt hx'
  exact (mem_map_iff e' D x).1 this

theorem card_le_of_elemAbelian (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (e : L ≃* ↥(ReeTag.G2.reeGamma K a))
    (hKR3 : ∀ (T : Sylow 3 L) (α : MulAut L),
      (∀ z ∈ (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L), α z = z) →
      ∃ u ∈ (T : Subgroup L), α = MulAut.conj u)
    (E : Subgroup (MulAut L)) (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ (3 ^ (2 * a + 1)) ^ 2 := by
  have hconj := conj_injective_of_equiv hK e
  have hcyc := isCyclic_outer_of_equiv ha hK e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : MulAut L →* Outer L := QuotientGroup.mk' (inner L) with hπ
  have hcard : Nat.card E = Nat.card (E.map π) * Nat.card (π.ker ⊓ E : Subgroup _) := by
    rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]
  have himg : Nat.card (E.map π) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨_, x, hx, rfl⟩ := y
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, ← map_pow, hE.2 x hx, map_one, OneMemClass.coe_one]
  set F₀ : Subgroup L := E.comap (MulAut.conj : L →* MulAut L) with hF₀
  have hker : Nat.card (π.ker ⊓ E : Subgroup _) ≤ Nat.card F₀ := by
    calc Nat.card (π.ker ⊓ E : Subgroup _) ≤ Nat.card (F₀.map MulAut.conj) :=
          Subgroup.card_le_of_le fun x hx => ?_
      _ = Nat.card F₀ := Subgroup.card_map_of_injective hconj
    rw [hπ, QuotientGroup.ker_mk', Subgroup.mem_inf] at hx
    obtain ⟨⟨y, rfl⟩, hxE⟩ := hx
    exact ⟨y, hxE, rfl⟩
  have hF₀3 : ∀ x ∈ F₀, x ^ 3 = 1 := by
    intro x hx
    apply hconj
    rw [map_pow, map_one]
    exact hE.2 _ hx
  have hF₀p : IsPGroup 3 F₀ := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hF₀3 _ x.2
  obtain ⟨T, hT⟩ := hF₀p.exists_le_sylow
  obtain ⟨hFle, hFgt⟩ := card_le_of_pow_three_le_sylow hK e T F₀ hT hF₀3
  by_cases hout : ∀ x ∈ E, π x = 1
  · have h1 : Nat.card (E.map π) = 1 := by
      rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff]
      exact fun x hx => hout x hx
    rw [hcard, h1, one_mul]
    exact hker.trans hFle
  · simp only [not_forall] at hout
    obtain ⟨y, hy, hy1⟩ := hout
    have hnot : ¬ (3 ^ (2 * a + 1)) ^ 2 < 3 * Nat.card F₀ := by
      intro hlt
      have hZT := hFgt hlt
      have hfix : ∀ z ∈ (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L),
          y z = z := by
        intro z hz
        have hzE : MulAut.conj z ∈ E := hZT hz
        have hcomm : y * MulAut.conj z = MulAut.conj z * y :=
          congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨_, hzE⟩)
        apply hconj
        have : y * MulAut.conj z * y⁻¹ = MulAut.conj (y z) := by
          ext w
          simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
            MulEquiv.apply_symm_apply]
        rw [← this, hcomm, mul_inv_cancel_right]
      obtain ⟨u, -, hyu⟩ := hKR3 T y hfix
      apply hy1
      rw [hπ, hyu, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨u, rfl⟩
    have h3 : Nat.card (E.map π) ≤ 3 := Nat.le_of_dvd (by norm_num) himg
    rw [hcard]
    calc Nat.card (E.map π) * Nat.card (π.ker ⊓ E : Subgroup _)
        ≤ 3 * Nat.card F₀ := Nat.mul_le_mul h3 hker
      _ ≤ (3 ^ (2 * a + 1)) ^ 2 := by omega

end Rank

end CFSG.AGLEmbedding.ReeModel
