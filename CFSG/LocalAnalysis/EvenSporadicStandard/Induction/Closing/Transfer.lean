module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Complement
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.TransferComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.TransferFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Fusion

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.ABGLocalTools

namespace ClosingSetup

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H} {t u : H} (S : ClosingSetup H N L t u)
include S

theorem false_of_transfer (hacc : AutCenterCond2 (↥L ⧸ center ↥L))
    (hout : OutTwo (↥L ⧸ center ↥L)) (hoc : AutOddCoreTrivial (↥L ⧸ center ↥L))
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (hu : twoAdic (L ⊓ centralizer ({u} : Set H)) < twoAdic L) (htN : t ∈ N) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := S.t_order
  have htt := S.t_mul_self
  have hNn : N.Normal := S.fstar.normal
  have hNs : IsSimpleGroup ↥N := S.fstar.isSimpleGroup
  have hnonab := S.fstar.nonabelian
  obtain ⟨K₀, hK₀C, hK₀odd, htK, hmul, hinv⟩ := exists_K₀ hS2 S.t_mem S.t_order
  set M : Subgroup H := centralizer ({t} : Set H) with hM
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  have huM : u ∈ M := mem_centralizer_singleton_iff.2 S.u_comm_t
  have hLM : L ≤ M := fun x hx => mem_centralizer_singleton_iff.2 (S.t_comm hx)
  have hMN := S.centralizer_t_le
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ L ⊔ K₀ := fun a ha b hb =>
    comm_mem_sup S.perfect hout hK₀C hmul hinv (hMN ha) (hMN hb)
  have hψ : (Abelianization.of (⟨t, htM⟩ : M)) ≠ 1 := by
    intro h1
    have h2 : (⟨t, htM⟩ : M) ∈ commutator M := by
      rw [← Abelianization.ker_of]
      exact h1
    have h3 : commutator M ≤ (L ⊔ K₀).subgroupOf M := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      exact hcomm a a.2 b b.2
    exact S.t_not_mem_sup hK₀C hK₀odd (h3 h2)
  obtain ⟨P, hPS, huP, htP⟩ : ∃ P : Subgroup H, IsSylowOf 2 P M ∧ u ∈ P ∧ t ∈ P := by
    have hu2 : IsPGroup 2 (zpowers (⟨u, huM⟩ : M)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, S.u_order, pow_one]
    have htcen : (⟨t, htM⟩ : M) ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
    have : (zpowers (⟨t, htM⟩ : M)).Normal :=
      Subgroup.normal_of_le_center (zpowers_le.2 htcen)
    have ht2' : IsPGroup 2 (zpowers (⟨t, htM⟩ : M)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
    obtain ⟨Q, hQ⟩ := hu2.exists_le_sylow
    have htQ := ht2'.le_sylow_of_normal Q
    exact ⟨Q.map M.subtype, ⟨Q, rfl⟩, ⟨_, hQ (mem_zpowers _), rfl⟩,
      ⟨_, htQ (mem_zpowers _), rfl⟩⟩
  have hPt : ∀ p ∈ P, p * t = t * p := fun p hp => mem_centralizer_singleton_iff.1 (hPS.le hp)
  obtain ⟨g, hgt, hgP⟩ := exists_conj_ne_centralizing_of_mem hnonab htN htt hPS.isPGroup htP hPt
    (Abelianization.of : M →* Abelianization M) hψ
  have hft : g * t * g⁻¹ ∈ fusedSet u t :=
    ⟨isConj_iff.2 ⟨g, rfl⟩, (hgP u huP).symm, (hgP t htP).symm⟩
  obtain ⟨u₁, hu₁N, t₂, ht₂N, hu₁, ht₂, hu₁₂, hu₁t, hνν, hσσ, hνσ, hfix, h1, h2⟩ :=
    S.fusion_pair hoc hft rfl
  rcases hacc _ _ hνν hσσ hνσ hfix with h3 | h3 | h3
  · exact h1 h3 hgt
  ·
    have h4 : g * t * g⁻¹ = u * t := h2 h3
    have hPu : ∀ p ∈ P, p * u = u * p := by
      intro p hp
      have e1 := hgP p hp
      rw [h4] at e1
      have e2 := hPt p hp
      apply mul_right_cancel (b := t)
      calc p * u * t = p * (u * t) := by group
        _ = (u * t) * p := e1
        _ = u * (t * p) := by group
        _ = u * (p * t) := by rw [e2]
        _ = u * p * t := by group
    have hS' : IsSylowOf 2 (P ⊓ L) L := hPS.inf_of_le_normalizer hLM hMN
    have hle : P ⊓ L ≤ L ⊓ centralizer ({u} : Set H) := fun x hx =>
      ⟨hx.2, mem_centralizer_singleton_iff.2 (hPu x hx.1)⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hS'.card_eq] at hdvd
    have hpos : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) ≠ 0 := Nat.card_pos.ne'
    exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 hdvd)
      (not_le.2 hu)
  · exfalso
    apply h3
    set P₂ : Subgroup H := P.map (MulAut.conj g⁻¹).toMonoidHom with hP₂
    have hP₂mem : ∀ x ∈ P₂, ∃ p ∈ P, x = g⁻¹ * p * g := by
      rintro x ⟨p, hp, rfl⟩
      exact ⟨p, hp, by simp⟩
    have hP₂M : P₂ ≤ M := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := hP₂mem x hx
      refine mem_centralizer_singleton_iff.2 ?_
      have e1 := hgP p hp
      calc g⁻¹ * p * g * t = g⁻¹ * (p * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * p) * g := by rw [e1]
        _ = t * (g⁻¹ * p * g) := by group
    have hP₂S : IsSylowOf 2 P₂ M := by
      refine isSylowOf_of_card hP₂M ?_
      rw [hP₂, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hPS.card_eq]
    have hS₂ : IsSylowOf 2 (P₂ ⊓ L) L := hP₂S.inf_of_le_normalizer hLM hMN
    set X : Subgroup ↥L := (P₂ ⊓ L).subgroupOf L with hX
    set f : ↥X →* (↥L ⧸ center ↥L) := (QuotientGroup.mk' (center ↥L)).comp X.subtype with hf
    have hfix : MonoidHom.range f ≤ fixSubgroup (normalizerAction L ⟨t₂, ht₂N⟩) := by
      rintro _ ⟨x, rfl⟩
      have hxP₂ : ((x : ↥L) : H) ∈ P₂ := (mem_subgroupOf.1 x.2).1
      obtain ⟨p, hp, hxp⟩ := hP₂mem _ hxP₂
      show normalizerAction L ⟨t₂, ht₂N⟩ ((QuotientGroup.mk' (center ↥L)) x) =
        (QuotientGroup.mk' (center ↥L)) x
      rw [QuotientGroup.mk'_apply, act_mk ht₂N]
      congr 1
      refine Subtype.ext ?_
      show t₂ * ((x : ↥L) : H) * t₂⁻¹ = x
      rw [hxp, ht₂]
      have e1 := hPt p hp
      calc g⁻¹ * t * g * (g⁻¹ * p * g) * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (t * p * t⁻¹) * g := by group
        _ = g⁻¹ * p * g := by rw [← e1]; group
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxZ : ((x : ↥L)) ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 hx
      have hxL : ((x : ↥L) : H) ∈ L := (x : ↥L).2
      have hxodd : Odd (orderOf ((x : ↥L) : H)) :=
        odd_orderOf_of_mem_center S.centre_odd hxL
          (fun y hy => congrArg Subtype.val (mem_center_iff.1 hxZ ⟨y, hy⟩))
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hP₂S.isPGroup
        (⟨((x : ↥L) : H), (mem_subgroupOf.1 x.2).1⟩ : ↥P₂)
      rw [Subgroup.orderOf_mk] at hj
      have h1 : orderOf ((x : ↥L) : H) = 1 := by
        rcases j with _ | j
        · simpa using hj
        · rw [hj] at hxodd
          exact absurd hxodd (by simp [Nat.odd_iff, pow_succ])
      have h2 : ((x : ↥L) : H) = 1 := orderOf_eq_one_iff.1 h1
      exact Subtype.ext (Subtype.ext h2)
    have hcardX : Nat.card X = 2 ^ (Nat.card ↥L).factorization 2 := by
      have : Nat.card X = Nat.card (P₂ ⊓ L : Subgroup H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P₂ ⊓ L ≤ L)).toEquiv
      rw [this, hS₂.card_eq]
    have hrange : Nat.card (MonoidHom.range f) = Nat.card X :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hL2 : (Nat.card ↥L).factorization 2 = (Nat.card (↥L ⧸ center ↥L)).factorization 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
      have hY0 : Nat.card (↥L ⧸ center ↥L) ≠ 0 := Nat.card_pos.ne'
      have hZ0 : Nat.card (center ↥L) ≠ 0 := Nat.card_pos.ne'
      have hZ2 : ¬ 2 ∣ Nat.card (center ↥L) := fun h =>
        (Nat.not_even_iff_odd.2 S.centre_odd) (even_iff_two_dvd.2 h)
      rw [h1, Nat.factorization_mul hY0 hZ0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hZ2, add_zero]
    show 2 ^ (Nat.card (↥L ⧸ center ↥L)).factorization 2 ∣
      Nat.card (fixSubgroup (normalizerAction L ⟨t₂, ht₂N⟩))
    rw [← hL2, ← hcardX, ← hrange]
    exact Subgroup.card_dvd_of_le hfix

end ClosingSetup

end CFSG.EvenSporadicStandard.Induction.Closing

