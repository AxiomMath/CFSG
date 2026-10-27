module

public import CFSG.LargeExtraspecial.S8KD
public import CFSG.LargeExtraspecial.S9GenD
public import CFSG.LargeExtraspecial.S8ThreeC
public import CFSG.LargeExtraspecial.S8ThreeD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem range_inf_eq_map_of_compl {K M : Type*} [Ring K] [AddCommGroup M] [Module K M]
    {A B : Submodule K M} (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = ⊥) (φ : M →ₗ[K] M)
    (hA : ∀ a ∈ A, φ a ∈ A) (hB : ∀ b ∈ B, φ b ∈ B) :
    LinearMap.range φ ⊓ A = A.map φ := by
  apply le_antisymm
  · rintro v ⟨⟨m, rfl⟩, hvA⟩
    have hm : m ∈ A ⊔ B := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    have hφb : φ b ∈ A ⊓ B := by
      refine ⟨?_, hB b hb⟩
      have := A.sub_mem hvA (hA a ha)
      rwa [map_add, add_sub_cancel_left] at this
    rw [hinf, Submodule.mem_bot] at hφb
    rw [map_add, hφb, add_zero]
    exact ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, hA a ha⟩

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commSub_le_self {X : Subgroup S.O} {τ : S.O} (hτ : τ ∈ normalizer (X : Set S.O)) :
    commSub S X τ ≤ X := by
  rw [commSub, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have h1 : τ * x⁻¹ * τ⁻¹ ∈ X := (mem_normalizer_iff.mp hτ _).mp (inv_mem hx)
  rw [show x * τ * x⁻¹ * τ⁻¹ = x * (τ * x⁻¹ * τ⁻¹) by group]
  exact mul_mem hx h1

section NQC

variable {t : S.O} [hN : NQHyp S g t]

theorem nqMk_inv' (n : Nbar S g t) : nqMk n⁻¹ = nqMk n :=
  (nqMk_eq_iff _ _).mpr (by simpa using hN.sq n n.2)

theorem nqMk_comm_eq' (σ : CMt S t) (n : Nbar S g t) :
    nqMk (n * S9.nConjC σ n⁻¹) = S9.nqLinC σ (nqMk n) + nqMk n := by
  rw [nqMk_mul, ← S9.nqLinC_mk]
  simp only [nqMk_inv']
  exact add_comm _ _

theorem nqRep_nqLinC_comm' {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hY : RmodN S g t = Y) (σ : CMt S t)
    (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t)
    (e : Y) (m : NQ S g t) :
    nqRep S g t hY e (S9.nqLinC σ m) = S9.nqLinC σ (nqRep S g t hY e m) := by
  have hm := nqMk_surjective (S := S) (g := g) (t := t) m
  obtain ⟨n, hn⟩ := hm
  subst hn
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hY]
    exact e.2
  rw [← range_resV hN.conj_mem t] at heR
  obtain ⟨r, hr⟩ := heR
  simp only [nqRep_apply hY hr.symm, S9.nqLinC_mk]
  rw [nqMk_eq_iff]
  simp only [S9.coe_nConjC, coe_nConj]
  have hc := hσR r r.2
  have hy := (nConj r (S9.nConjC σ n)).2
  simp only [coe_nConj, S9.coe_nConjC] at hy
  convert hN.comm _ (inv_mem hy) _ hc using 1
  group

end NQC

variable (S g) in
@[expose] noncomputable def nqComm (t : S.O) [NQHyp S g t] (σ : CMt S t) :
    NQ S g t →ₗ[ZMod 2] NQ S g t :=
  S9.nqLinC σ + LinearMap.id

theorem nqComm_apply {t : S.O} [NQHyp S g t] (σ : CMt S t) (v : NQ S g t) :
    nqComm S g t σ v = S9.nqLinC σ v + v :=
  rfl

theorem nqComm_mk {t : S.O} [NQHyp S g t] (σ : CMt S t) (n : Nbar S g t)
    (hc : (n : S.O) * σ * (n : S.O)⁻¹ * (σ : S.O)⁻¹ ∈ Nbar S g t) :
    nqComm S g t σ (nqMk n) = nqMk ⟨_, hc⟩ := by
  have e : (⟨_, hc⟩ : Nbar S g t) = n * S9.nConjC σ n⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, S9.coe_nConjC, Subgroup.coe_inv]
    group)
  rw [e, nqMk_comm_eq']
  exact (nqComm_apply σ _).symm

theorem nqComm_mem_fixOf {t : S.O} [NQHyp S g t] {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hY : RmodN S g t = Y) (σ : CMt S t)
    (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t)
    {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} {v : NQ S g t}
    (hv : v ∈ S2.fixOf (nqRep S g t hY) T) :
    nqComm S g t σ v ∈ S2.fixOf (nqRep S g t hY) T := by
  have hv' := (S2.mem_fixOf _).mp hv
  refine (S2.mem_fixOf _).mpr fun e he => ?_
  have h1 := hv' e he
  simp only [nqComm_apply, map_add, nqRep_nqLinC_comm' hY σ hσR, h1]

theorem nqComm_mem_range {t : S.O} [NQHyp S g t] {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hY : RmodN S g t = Y) (σ : CMt S t)
    (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t) (e : Y)
    {v : NQ S g t} (hv : v ∈ LinearMap.range (nqComm S g t σ)) :
    nqRep S g t hY e v ∈ LinearMap.range (nqComm S g t σ) := by
  obtain ⟨m, hm⟩ := hv
  subst hm
  refine ⟨nqRep S g t hY e m, ?_⟩
  simp only [nqComm_apply, map_add, nqRep_nqLinC_comm' hY σ hσR]

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem comm_mem_Nbar_of_fix' (H : Hyp4 S g) {τ : S.O} (hτK : τ ∈ CMt S t)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∀ r ∈ Rbar S g t, ((⟨τ, hτK⟩ : CMt S t) : S.O) * r *
      ((⟨τ, hτK⟩ : CMt S t) : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t := fun r hr => by
  obtain ⟨hτM, hτt⟩ := mem_CMt.mp hτK
  have h1 := inv_mem (comm_mem_Nbar_of_fix H hτM hτt hτV hr)
  rwa [show (r * τ * r⁻¹ * τ⁻¹)⁻¹ = τ * r * τ⁻¹ * r⁻¹ by group] at h1

theorem finrank_range_nqComm_aux (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) [NQHyp S g t] {τ : S.O} (hτK : τ ∈ CMt S t)
    (hσR : ∀ r ∈ Rbar S g t, ((⟨τ, hτK⟩ : CMt S t) : S.O) * r *
      ((⟨τ, hτK⟩ : CMt S t) : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t) :
    2 ^ (D.m - 1) ∣ finrank (ZMod 2) (LinearMap.range (nqComm S g t ⟨τ, hτK⟩)) ∧
      finrank (ZMod 2) (LinearMap.range (nqComm S g t ⟨τ, hτK⟩)) =
        2 * finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) := by
  have hD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ D.hN0 D.hh D.hb D.hX D.hE
  have : FiniteDimensional (ZMod 2) (NQ S g t) := inferInstance
  obtain ⟨hdvd, -, htwo⟩ := dvd_and_two_mul_of_invariant (nqRep S g t D.hX) D.hm D.hdim
    (aV_ne_zero H ht) D.hQa D.Q_bV D.polar_aV_bV hD
    (fun e v hv => nqComm_mem_range D.hX ⟨τ, hτK⟩ hσR e hv)
  refine ⟨hdvd, htwo.trans ?_⟩
  obtain ⟨hsup, hinf⟩ := hD
  simp only [top_inf_eq] at hsup hinf
  have key := range_inf_eq_map_of_compl hsup hinf (nqComm S g t ⟨τ, hτK⟩)
    (fun a ha => nqComm_mem_fixOf D.hX _ hσR ha) (fun b hb => nqComm_mem_fixOf D.hX _ hσR hb)
  have key3 := key.trans
    (congrArg (Submodule.map (nqComm S g t ⟨τ, hτK⟩)) (fixOf_nqRep_radFix_eq hNo D))
  exact congrArg (fun K : Submodule (ZMod 2) (NQ S g t) => 2 * finrank (ZMod 2) ↥K)
    key3

theorem finrank_range_nqComm (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) [NQHyp S g t] {τ : S.O} (hτK : τ ∈ CMt S t)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    2 ^ (D.m - 1) ∣ finrank (ZMod 2) (LinearMap.range (nqComm S g t ⟨τ, hτK⟩)) ∧
      finrank (ZMod 2) (LinearMap.range (nqComm S g t ⟨τ, hτK⟩)) =
        2 * finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) :=
  finrank_range_nqComm_aux hNo hΩ D hτK (comm_mem_Nbar_of_fix' H hτK hτV)

theorem exists_surjective_commSub_Abar (H : Hyp4 S g) (ht : t ∈ S.Lbar g) [NQHyp S g t]
    {τ : S.O} (hτK : τ ∈ CMt S t) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∃ f : commSub S (S.Lbar g ⊓ Nbar S g t) τ →
        (nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩),
      Function.Surjective f ∧ ∀ (k : commSub S (S.Lbar g ⊓ Nbar S g t) τ)
        (hk : (k : S.O) ∈ Nbar S g t), (f k : NQ S g t) = nqMk ⟨k, hk⟩ := by
  obtain ⟨hτM, hτt⟩ := mem_CMt.mp hτK
  have hle : commSub S (S.Lbar g ⊓ Nbar S g t) τ ≤ Nbar S g t :=
    (commSub_le_self (mem_normalizer_Abar_of_fix H ht hτM hτt hτV)).trans inf_le_right
  have hcN : ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ Nbar S g t := fun n hn => by
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hτM
    have h1 := conj_mem_Nbar H.conj_mem (k := k) (by rw [hk]; exact hτt) (inv_mem hn)
    rw [hk] at h1
    rw [show n * τ * n⁻¹ * τ⁻¹ = n * (τ * n⁻¹ * τ⁻¹) by group]
    exact mul_mem hn h1
  have hmem : ∀ k ∈ commSub S (S.Lbar g ⊓ Nbar S g t) τ, ∀ hk : k ∈ Nbar S g t,
      nqMk ⟨k, hk⟩ ∈ (nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩) := by
    intro k hkC
    induction hkC using closure_induction with
    | mem c hc =>
      obtain ⟨α, hα, rfl⟩ := hc
      intro hk
      have e := nqComm_mk (⟨τ, hτK⟩ : CMt S t) ⟨α, hα.2⟩ hk
      exact ⟨nqMk ⟨α, hα.2⟩, ⟨⟨α, hα.2⟩, hα.1, rfl⟩, e⟩
    | one =>
      intro hk
      have h0 : nqMk (⟨1, hk⟩ : Nbar S g t) = 0 := (nqMk_eq_zero_iff _).mpr (one_mem _)
      rw [h0]
      exact zero_mem _
    | mul x y hx hy ihx ihy =>
      intro hk
      exact Submodule.add_mem _ (ihx (hle hx)) (ihy (hle hy))
    | inv x hx ihx =>
      intro hk
      have h2 : nqMk (⟨x⁻¹, hk⟩ : Nbar S g t) = nqMk ⟨x, hle hx⟩ := nqMk_inv' ⟨x, hle hx⟩
      rw [h2]
      exact ihx (hle hx)
  refine ⟨fun k => ⟨nqMk ⟨k, hle k.2⟩, hmem k k.2 (hle k.2)⟩, ?_, fun k hk => rfl⟩
  rintro ⟨v, m, ⟨n, hnL, rfl⟩, rfl⟩
  refine ⟨⟨_, comm_mem_commSub ⟨hnL, n.2⟩⟩, Subtype.ext ?_⟩
  exact (nqComm_mk (⟨τ, hτK⟩ : CMt S t) n (hcN _ n.2)).symm

theorem exists_comm_not_mem_zpowers (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t) :
    ∃ α ∈ S.Lbar g ⊓ Nbar S g t, α * τ * α⁻¹ * τ⁻¹ ∉ zpowers t := by
  by_contra hcon
  push Not at hcon
  exact false_of_Abar_comm_mem_zpowers D hm3 hfus hsub hxM hxτ hτt hτV hτN hcon

theorem one_lt_card_map_nqComm (H : Hyp4 S g) (ht : t ∈ S.Lbar g) [NQHyp S g t] {τ : S.O}
    (hτK : τ ∈ CMt S t) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {α : S.O}
    (hα : α ∈ S.Lbar g ⊓ Nbar S g t) (hαt : α * τ * α⁻¹ * τ⁻¹ ∉ zpowers t) :
    1 < Nat.card ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) := by
  obtain ⟨hτM, hτt⟩ := mem_CMt.mp hτK
  obtain ⟨f, -, hfv⟩ := exists_surjective_commSub_Abar H ht hτK hτV
  have hk := comm_mem_commSub (τ := τ) hα
  have hkN : α * τ * α⁻¹ * τ⁻¹ ∈ Nbar S g t :=
    (commSub_le_self (mem_normalizer_Abar_of_fix H ht hτM hτt hτV)).trans inf_le_right hk
  have hne : f ⟨_, hk⟩ ≠ f 1 := by
    intro h
    apply hαt
    have h1 : nqMk ⟨_, hkN⟩ = nqMk ⟨1, one_mem _⟩ :=
      ((hfv ⟨_, hk⟩ hkN).symm.trans (congrArg Subtype.val h)).trans (hfv 1 (one_mem _))
    have h2 := inv_mem ((nqMk_eq_iff _ _).mp h1)
    change ((α * τ * α⁻¹ * τ⁻¹)⁻¹ * 1)⁻¹ ∈ zpowers t at h2
    rwa [mul_one, inv_inv] at h2
  exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hne⟩⟩

theorem two_pow_finrank_map_nqComm_le (H : Hyp4 S g) (ht : t ∈ S.Lbar g) [NQHyp S g t]
    {τ : S.O} (hτK : τ ∈ CMt S t) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    2 ^ finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) ≤
      Nat.card (commSub S (S.Lbar g ⊓ Nbar S g t) τ) := by
  obtain ⟨f, hfs, -⟩ := exists_surjective_commSub_Abar H ht hτK hτV
  exact (FiniteField.pow_finrank_eq_natCard 2 _).trans_le (Nat.card_le_card_of_surjective f hfs)

theorem finrank_map_nqComm_pos (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] (hτK : τ ∈ CMt S t) :
    0 < finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) := by
  obtain ⟨α, hα, hαt⟩ := exists_comm_not_mem_zpowers D hm3 hfus hsub hxM hxτ hτt hτV hτN
  have h1 := one_lt_card_map_nqComm H ht hτK hτV hα hαt
  have h2 := FiniteField.pow_finrank_eq_natCard 2
    ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩))
  by_contra h0
  push Not at h0
  rw [Nat.le_zero.mp h0, pow_zero] at h2
  omega

theorem finrank_map_nqComm_le_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] (hτK : τ ∈ CMt S t) :
    finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) ≤ 4 := by
  have hle := two_pow_finrank_map_nqComm_le H ht hτK hτV
  obtain ⟨hAL, hle4⟩ := card_commSub_le_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN
  have hle4' : Nat.card (commSub S (S.Lbar g ⊓ Nbar S g t) τ) ≤ 2 ^ 4 :=
    (congrArg (fun X : Subgroup S.O => Nat.card ↥X) hAL).trans_le hle4
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hle.trans hle4')

theorem four_dvd_finrank_map_nqComm (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4) [NQHyp S g t] {τ : S.O} (hτK : τ ∈ CMt S t)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    4 ∣ finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) := by
  obtain ⟨hdvd, htwo⟩ := finrank_range_nqComm hNo hΩ D hτK hτV
  rw [htwo, hm4] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  norm_num at hc
  exact ⟨c, by omega⟩

theorem finrank_map_nqComm_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] (hτK : τ ∈ CMt S t) :
    finrank (ZMod 2) ((nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩)) = 4 := by
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  have h1 := finrank_map_nqComm_pos D (by omega) hfus hsub hxM hxτ hτt hτV hτN hτK
  have h2 := finrank_map_nqComm_le_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN hτK
  obtain ⟨c, hc⟩ := four_dvd_finrank_map_nqComm hNo hΩ D hm4 hτK hτV
  omega

theorem nqMk_mem_range_of_mem_N1bar (H : Hyp4 S g) [NQHyp S g t]
    {τ : S.O} (hτK : τ ∈ CMt S t) (hle : N1bar S g t τ ≤ Nbar S g t) {ν : S.O}
    (hν : ν ∈ N1bar S g t τ) (hνN : ν ∈ Nbar S g t) :
    nqMk ⟨ν, hνN⟩ ∈ LinearMap.range (nqComm S g t ⟨τ, hτK⟩) := by
  obtain ⟨hτM, hτt⟩ := mem_CMt.mp hτK
  have hcN : ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ Nbar S g t := fun n hn => by
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hτM
    have h1 := conj_mem_Nbar H.conj_mem (k := k) (by rw [hk]; exact hτt) (inv_mem hn)
    rw [hk] at h1
    rw [show n * τ * n⁻¹ * τ⁻¹ = n * (τ * n⁻¹ * τ⁻¹) by group]
    exact mul_mem hn h1
  revert hνN
  induction hν using closure_induction with
  | mem c hc =>
    intro hk
    rcases hc with hc | ⟨n, hn, hc⟩
    · have h0 : nqMk (⟨c, hk⟩ : Nbar S g t) = 0 := (nqMk_eq_zero_iff _).mpr (by
        change c ∈ zpowers t
        rw [hc]
        exact mem_zpowers t)
      rw [h0]
      exact zero_mem _
    · have h3 : nqMk (⟨c, hk⟩ : Nbar S g t) = nqMk ⟨n * τ * n⁻¹ * τ⁻¹, hcN n hn⟩ := by
        congr 1
        exact Subtype.ext hc
      rw [h3]
      exact ⟨nqMk ⟨n, hn⟩, nqComm_mk (⟨τ, hτK⟩ : CMt S t) ⟨n, hn⟩ (hcN n hn)⟩
  | one =>
    intro hk
    have h0 : nqMk (⟨1, hk⟩ : Nbar S g t) = 0 := (nqMk_eq_zero_iff _).mpr (one_mem _)
    rw [h0]
    exact zero_mem _
  | mul x y hx hy ihx ihy =>
    intro hk
    exact Submodule.add_mem _ (ihx (hle hx)) (ihy (hle hy))
  | inv x hx ihx =>
    intro hk
    have h2 : nqMk (⟨x⁻¹, hk⟩ : Nbar S g t) = nqMk ⟨x, hle hx⟩ := nqMk_inv' ⟨x, hle hx⟩
    rw [h2]
    exact ihx (hle hx)

theorem coe_mem_zpowers_of_mem {X : Type*} [Group X] {K : Subgroup X} {t : X} (htK : t ∈ K)
    {x : K} (h : x ∈ zpowers (⟨t, htK⟩ : K)) : (x : X) ∈ zpowers t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp h
  exact ⟨k, by simp⟩

end CFSG.LargeExtraspecial.S8
