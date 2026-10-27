module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab

open scoped commutatorElement

@[expose] def SolvNormalCentral (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N ≤ Subgroup.center G

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem not_isSolvable_of_isQuasisimple {G : Type*} [Group G] (hG : CFSG.Open.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hsolv
  obtain ⟨hp, hs⟩ := hG
  haveI : Nontrivial G := (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne hp

theorem solvNormalCentral_of_isQuasisimple {G : Type*} [Group G]
    (hG : CFSG.Open.IsQuasisimple G) : SolvNormalCentral G := by
  intro N hN hNs
  rcases normal_eq_top_or_le_center hG hN with htop | hc
  · exfalso
    subst htop
    exact not_isSolvable_of_isQuasisimple hG
      (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
        Subgroup.topEquiv.surjective)
  · exact hc

theorem solvNormalCentral_of_commutative {G : Type*} [Group G]
    (h : ∀ a b : G, a * b = b * a) : SolvNormalCentral G :=
  fun _ _ _ x _ => Subgroup.mem_center_iff.mpr fun g => h g x

theorem solvNormalCentral_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : SolvNormalCentral G) : SolvNormalCentral H := by
  intro N hN hNs x hx
  have hN' : (N.comap e.toMonoidHom).Normal := hN.comap _
  haveI : Group.IsSolvable ↥(N.comap e.toMonoidHom) := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (e.toMonoidHom.comp (N.comap e.toMonoidHom).subtype).codRestrict N fun y => y.2) ?_
    intro a b hab
    exact Subtype.ext (e.injective (congrArg Subtype.val hab))
  have hx' : e.symm x ∈ N.comap e.toMonoidHom := by simpa using hx
  have hc := Subgroup.mem_center_iff.mp (h _ hN' inferInstance hx')
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg e (hc (e.symm g))
  simpa using this

theorem commute_of_solvable_of_isQuasisimple {H : Type*} [Group H] {S N : Subgroup H}
    (hS : CFSG.Open.IsQuasisimple ↥S) (hN : Group.IsSolvable ↥N)
    (hSN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hNS : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) :
    ∀ n ∈ N, ∀ s ∈ S, n * s = s * n := by
  have hTn : ((N ⊓ S).subgroupOf S).Normal := by
    refine ⟨fun t ht s => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa using hSN s s.2 t (Subgroup.mem_inf.mp ht).1
    · simpa using S.mul_mem (S.mul_mem s.2 t.2) (S.inv_mem s.2)
  have hTsolv : Group.IsSolvable ↥((N ⊓ S).subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion (inf_le_left : N ⊓ S ≤ N)).comp
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ S ≤ S)).toMonoidHom)
      ((Subgroup.inclusion_injective (inf_le_left : N ⊓ S ≤ N)).comp
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ S ≤ S)).injective)
  have hTcenter : (N ⊓ S).subgroupOf S ≤ Subgroup.center ↥S := by
    rcases normal_eq_top_or_le_center hS hTn with htop | hc
    · exfalso
      apply not_isSolvable_of_isQuasisimple hS
      rw [htop] at hTsolv
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup ↥S) ≃* ↥S).toMonoidHom)
        Subgroup.topEquiv.surjective
    · exact hc
  have hcomm_le : ⁅N, S⁆ ≤ N ⊓ S := by
    rw [Subgroup.commutator_le]
    intro n hn s hs
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : s * n⁻¹ * s⁻¹ ∈ N := hSN s hs n⁻¹ (N.inv_mem hn)
      rw [commutatorElement_def]
      simpa [mul_assoc] using N.mul_mem hn h1
    · have h1 : n * s * n⁻¹ ∈ S := hNS n hn s hs
      rw [commutatorElement_def]
      exact S.mul_mem h1 (S.inv_mem hs)
  have hcomm : ∀ x ∈ ⁅N, S⁆, ∀ y ∈ S, y * x = x * y := by
    intro x hx y hy
    have hxNS : x ∈ N ⊓ S := hcomm_le hx
    have hxS : x ∈ S := (Subgroup.mem_inf.mp hxNS).2
    have hc : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S :=
      hTcenter (by rw [Subgroup.mem_subgroupOf]; exact hxNS)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
  have h1 : ⁅⁅N, S⁆, S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm x hx y hy
  have h2 : ⁅⁅S, N⁆, S⁆ = ⊥ := by
    rw [← Subgroup.commutator_comm N S]
    exact h1
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := S) (H₂ := S) (H₃ := N) h2 h1
  have hperf : ⁅S, S⁆ = S := by
    rw [← Subgroup.map_subtype_commutator S, hS.1, Subgroup.map_top, Subgroup.range_subtype]
  rw [hperf] at hrot
  have hbot : ⁅N, S⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
  intro n hn s hs
  have hmem : ⁅n, s⁆ ∈ ⁅N, S⁆ := Subgroup.commutator_mem_commutator hn hs
  rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
  calc n * s = (n * s * n⁻¹ * s⁻¹) * (s * n) := by group
    _ = s * n := by rw [hmem, one_mul]

theorem isSolvable_comap_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hk : Group.IsSolvable ↥f.ker) (M : Subgroup B)
    (hM : Group.IsSolvable ↥M) : Group.IsSolvable ↥(M.comap f) := by
  set h : ↥(M.comap f) →* B := f.comp (M.comap f).subtype with hh
  have hrange : h.range = M := by
    ext y
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ha
    · intro hy
      obtain ⟨a, rfl⟩ := hf y
      exact ⟨⟨a, hy⟩, rfl⟩
  haveI hker : Group.IsSolvable ↥h.ker := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := ((M.comap f).subtype.comp h.ker.subtype).codRestrict f.ker fun x => x.2) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  haveI hr : Group.IsSolvable ↥h.range := by
    rw [hrange]
    exact hM
  exact Group.isSolvable_of_ker_le_range h.ker.subtype h.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem solvNormalCentral_quotPCore {Q P' Λ : Type*} [Group Q] [Group P'] [Group Λ] [Finite P']
    (φ : Q →* P') (hφ : Function.Surjective φ) (hφk : Group.IsSolvable ↥φ.ker)
    (β : Q →* Λ) (hβ : Function.Surjective β) (hβk : IsPGroup 2 ↥β.ker)
    (hΛ : SolvNormalCentral Λ) : SolvNormalCentral (P' ⧸ CFSG.pCore 2 P') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro N hN hNs
  set ψ : Q →* P' ⧸ CFSG.pCore 2 P' := (QuotientGroup.mk' (CFSG.pCore 2 P')).comp φ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψk : Group.IsSolvable ↥ψ.ker := by
    have hker : ψ.ker = (CFSG.pCore 2 P').comap φ := by
      ext x
      simp [hψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [hker]
    exact isSolvable_comap_of_surjective φ hφ hφk _
      (by haveI := CFSG.pCore_isNilpotent (p := 2) (G := P'); infer_instance)
  haveI hOs : Group.IsSolvable ↥(N.comap ψ) :=
    isSolvable_comap_of_surjective ψ hψs hψk N hNs
  have hkerβ : β.ker ≤ ψ.ker := by
    have hnorm : (β.ker.map φ).Normal := β.normal_ker.map φ hφ
    have hle : β.ker.map φ ≤ CFSG.pCore 2 P' := le_sSup ⟨hnorm, hβk.map φ⟩
    intro k hk
    exact (QuotientGroup.eq_one_iff _).mpr (hle ⟨k, hk, rfl⟩)
  haveI : Group.IsSolvable ↥((N.comap ψ).map β) :=
    Group.isSolvable_of_surjective (f := β.subgroupMap (N.comap ψ))
      (β.subgroupMap_surjective (N.comap ψ))
  have hcentral : (N.comap ψ).map β ≤ Subgroup.center Λ :=
    hΛ _ ((hN.comap ψ).map β hβ) inferInstance
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x', rfl⟩ := hψs x
  obtain ⟨y', rfl⟩ := hψs y
  have hx' : x' ∈ N.comap ψ := hx
  have hc := Subgroup.mem_center_iff.mp (hcentral ⟨x', hx', rfl⟩) (β y')
  have hker : y' * x' * (x' * y')⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
  have := hkerβ hker
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_mul, mul_inv_eq_one] at this
  exact this

theorem pCoreOf_top_eq (p : ℕ) (G : Type*) [Group G] :
    CFSG.Open.pCoreOf p (⊤ : Subgroup G) = CFSG.pCore p G := by
  unfold CFSG.Open.pCoreOf
  exact CFSG.pCore_map_iso p (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

theorem isEmpty_quotPCore_perm_three {X : Type*} [Group X] [Finite X] {P R : Subgroup X}
    (hP : SolvNormalCentral (↥P ⧸ CFSG.pCore 2 ↥P)) (hRP : R ≤ P)
    (hRs : CFSG.Open.IsSubnormal R P) :
    IsEmpty (↥R ⧸ CFSG.pCore 2 ↥R ≃* Equiv.Perm (Fin 3)) := by
  refine ⟨fun e => ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥P →* ↥P ⧸ CFSG.pCore 2 ↥P := QuotientGroup.mk' (CFSG.pCore 2 ↥P) with hπ
  set ι : ↥R →* ↥P := Subgroup.inclusion hRP with hι
  set φ : ↥R →* ↥P ⧸ CFSG.pCore 2 ↥P := π.comp ι with hφ
  have hι_inj : Function.Injective ι := Subgroup.inclusion_injective hRP
  have hmem : ∀ r : ↥R, φ r = 1 ↔ ι r ∈ CFSG.pCore 2 ↥P := fun r =>
    QuotientGroup.eq_one_iff (ι r)
  have hker : φ.ker = CFSG.pCore 2 ↥R := by
    apply le_antisymm
    · have hker' : φ.ker = (CFSG.pCore 2 ↥P).comap ι := by
        ext r
        exact hmem r
      have hp : IsPGroup 2 ↥φ.ker := by
        rw [hker']
        exact CFSG.pCore_isPGroup.comap_of_injective ι hι_inj
      exact le_sSup ⟨φ.normal_ker, hp⟩
    · intro r hr
      have h1 : CFSG.Open.pCoreOf 2 R ≤ CFSG.Open.pCoreOf 2 P :=
        CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 hRs
      obtain ⟨p, hp, hpr⟩ := h1 (⟨r, hr, rfl⟩ : (r : X) ∈ CFSG.Open.pCoreOf 2 R)
      have : ι r = p := Subtype.ext hpr.symm
      exact (hmem r).mpr (this ▸ hp)
  let eR : φ.range ≃* ↥R ⧸ CFSG.pCore 2 ↥R :=
    (QuotientGroup.quotientKerEquivRange φ).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)
  let e' : φ.range ≃* Equiv.Perm (Fin 3) := eR.trans e
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  set s : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hs
  have hc3 : c ^ 3 = 1 := by decide
  have hcs : c * s ≠ s * c := by decide
  have hconj : ∀ g : Equiv.Perm (Fin 3), g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹ := by decide
  have hcn : (Subgroup.zpowers c).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow]
    rcases hconj g with h | h <;> rw [h]
    · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
    · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) k
  set x₀ : φ.range := e'.symm c with hx₀
  set y₀ : φ.range := e'.symm s with hy₀
  have hx₀3 : x₀ ^ 3 = 1 := by rw [hx₀, ← map_pow, hc3, map_one]
  set A : Subgroup φ.range := Subgroup.zpowers x₀ with hA
  have hAp : IsPGroup 3 ↥A := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx₀3, one_zpow]
  have hAn : A.Normal := by
    have : A = (Subgroup.zpowers c).map e'.symm.toMonoidHom := by
      rw [hA, MonoidHom.map_zpowers]
      rfl
    rw [this]
    exact hcn.map _ e'.symm.surjective
  set A' : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P) := A.map φ.range.subtype with hA'
  have hsubR : CFSG.Open.IsSubnormal φ.range (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) := by
    have h1 : CFSG.Open.IsSubnormal (R.subgroupOf P) (⊤ : Subgroup ↥P) :=
      CFSG.Open.IsSubnormal.top_iff.mpr (CFSG.Open.IsSubnormal.subgroupOf hRs)
    have h2 := CFSG.Open.IsSubnormal.map π h1
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h2
    have hrange : ι.range = R.subgroupOf P := by
      ext x
      constructor
      · rintro ⟨r, rfl⟩
        exact r.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    have h3 : φ.range = (R.subgroupOf P).map π := by
      rw [hφ, MonoidHom.range_comp, hrange]
    rw [h3]
    exact h2
  have hsubA : CFSG.Open.IsSubnormal A' ⊤ := by
    refine CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le A) ?_ hsubR
    change (Subgroup.comap φ.range.subtype (A.map φ.range.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective φ.range.subtype_injective A]
    exact hAn
  have hle : A' ≤ CFSG.pCore 3 (↥P ⧸ CFSG.pCore 2 ↥P) := by
    have h := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 3 hsubA
      (hAp.map φ.range.subtype)
    rwa [pCoreOf_top_eq] at h
  have hcenter := hP (CFSG.pCore 3 (↥P ⧸ CFSG.pCore 2 ↥P)) inferInstance
    (by
      haveI := CFSG.pCore_isNilpotent (p := 3) (G := ↥P ⧸ CFSG.pCore 2 ↥P)
      infer_instance)
  have hx : ((x₀ : φ.range) : ↥P ⧸ CFSG.pCore 2 ↥P) ∈ CFSG.pCore 3 (↥P ⧸ CFSG.pCore 2 ↥P) :=
    hle ⟨x₀, Subgroup.mem_zpowers x₀, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp (hcenter hx) ((y₀ : φ.range) : ↥P ⧸ CFSG.pCore 2 ↥P)
  have hcomm' : y₀ * x₀ = x₀ * y₀ := Subtype.ext hcomm
  have := congrArg e' hcomm'
  rw [map_mul, map_mul, hy₀, hx₀, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  exact hcs this.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
